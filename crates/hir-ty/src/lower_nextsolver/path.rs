//! A wrapper around [`TyLoweringContext`] specifically for lowering paths.

use std::iter;

use either::Either;
use hir_def::{
    GenericDefId, GenericParamId, ItemContainerId, Lookup, TraitId,
    builtin_type::BuiltinType,
    expr_store::{
        HygieneId,
        path::{GenericArg, GenericArgs, GenericArgsParentheses, Path, PathSegment, PathSegments},
    },
    hir::generics::GenericParamDataRef,
    resolver::{ResolveValueResult, TypeNs, ValueNs},
    signatures::TraitFlags,
    type_ref::TypeRef,
};
use intern::sym;
use rustc_type_ir::{
    AliasTerm, AliasTy, AliasTyKind,
    inherent::{GenericArgs as _, SliceLike, Ty as _},
};
use smallvec::SmallVec;
use stdx::never;

use crate::{
    GenericArgsProhibitedReason, PathLoweringDiagnostic, TyDefId, ValueTyDefId,
    consteval_nextsolver::{unknown_const, unknown_const_as_generic},
    generics::generics,
    lower::PathDiagnosticCallbackData,
    lower_nextsolver::{impl_self_ty_query, lower_generic_arg},
    next_solver::{
        AdtDef, Binder, Clause, DbInterner, ErrorGuaranteed, Predicate, ProjectionPredicate,
        Region, SolverDefId, TraitRef, Ty,
        mapping::ChalkToNextSolver,
        util::apply_args_to_binder,
    },
    primitive,
};

use super::{
    ImplTraitLoweringMode, TyLoweringContext, associated_type_by_name_including_super_traits,
    const_param_ty_query, named_associated_type_shorthand_candidates, ty_query,
};

type CallbackData<'a> =
    Either<PathDiagnosticCallbackData, crate::infer::diagnostics::PathDiagnosticCallbackData<'a>>;

// We cannot use `&mut dyn FnMut()` because of lifetime issues, and we don't want to use `Box<dyn FnMut()>`
// because of the allocation, so we create a lifetime-less callback, tailored for our needs.
pub(crate) struct PathDiagnosticCallback<'a, 'db> {
    pub(crate) data: CallbackData<'a>,
    pub(crate) callback:
        fn(&CallbackData<'_>, &mut TyLoweringContext<'db, '_>, PathLoweringDiagnostic),
}

pub(crate) struct PathLoweringContext<'a, 'b, 'db: 'a + 'b> {
    ctx: &'a mut TyLoweringContext<'db, 'b>,
    on_diagnostic: PathDiagnosticCallback<'a, 'db>,
    path: &'a Path,
    segments: PathSegments<'a>,
    current_segment_idx: usize,
    /// Contains the previous segment if `current_segment_idx == segments.len()`
    current_or_prev_segment: PathSegment<'a>,
}

impl<'a, 'b, 'db> PathLoweringContext<'a, 'b, 'db> {
    #[inline]
    pub(crate) fn new(
        ctx: &'a mut TyLoweringContext<'db, 'b>,
        on_diagnostic: PathDiagnosticCallback<'a, 'db>,
        path: &'a Path,
    ) -> Self {
        let segments = path.segments();
        let first_segment = segments.first().unwrap_or(PathSegment::MISSING);
        Self {
            ctx,
            on_diagnostic,
            path,
            segments,
            current_segment_idx: 0,
            current_or_prev_segment: first_segment,
        }
    }

    #[inline]
    #[cold]
    fn on_diagnostic(&mut self, diag: PathLoweringDiagnostic) {
        (self.on_diagnostic.callback)(&self.on_diagnostic.data, self.ctx, diag);
    }

    #[inline]
    pub(crate) fn ty_ctx(&mut self) -> &mut TyLoweringContext<'db, 'b> {
        self.ctx
    }

    #[inline]
    fn current_segment_u32(&self) -> u32 {
        self.current_segment_idx as u32
    }

    #[inline]
    fn skip_resolved_segment(&mut self) {
        if !matches!(self.path, Path::LangItem(..)) {
            // In lang items, the resolved "segment" is not one of the segments. Perhaps we should've put it
            // point at -1, but I don't feel this is clearer.
            self.current_segment_idx += 1;
        }
        self.update_current_segment();
    }

    #[inline]
    fn update_current_segment(&mut self) {
        self.current_or_prev_segment =
            self.segments.get(self.current_segment_idx).unwrap_or(self.current_or_prev_segment);
    }

    #[inline]
    pub(crate) fn ignore_last_segment(&mut self) {
        self.segments = self.segments.strip_last();
    }

    #[inline]
    pub(crate) fn set_current_segment(&mut self, segment: usize) {
        self.current_segment_idx = segment;
        self.current_or_prev_segment = self
            .segments
            .get(segment)
            .expect("invalid segment passed to PathLoweringContext::set_current_segment()");
    }

    pub(crate) fn lower_ty_relative_path(
        &mut self,
        ty: Ty<'db>,
        // We need the original resolution to lower `Self::AssocTy` correctly
        res: Option<TypeNs>,
    ) -> (Ty<'db>, Option<TypeNs>) {
        let remaining_segments = self.segments.len() - self.current_segment_idx;
        match remaining_segments {
            0 => (ty, res),
            1 => {
                // resolve unselected assoc types
                (self.select_associated_type(res), None)
            }
            _ => {
                // FIXME report error (ambiguous associated type)
                (Ty::new_error(self.ctx.interner, ErrorGuaranteed), None)
            }
        }
    }

    fn prohibit_parenthesized_generic_args(&mut self) -> bool {
        if let Some(generic_args) = self.current_or_prev_segment.args_and_bindings {
            match generic_args.parenthesized {
                GenericArgsParentheses::No => {}
                GenericArgsParentheses::ReturnTypeNotation | GenericArgsParentheses::ParenSugar => {
                    let segment = self.current_segment_u32();
                    self.on_diagnostic(
                        PathLoweringDiagnostic::ParenthesizedGenericArgsWithoutFnTrait { segment },
                    );
                    return true;
                }
            }
        }
        false
    }

    // When calling this, the current segment is the resolved segment (we don't advance it yet).
    pub(crate) fn lower_partly_resolved_path(
        &mut self,
        resolution: TypeNs,
        infer_args: bool,
    ) -> (Ty<'db>, Option<TypeNs>) {
        let remaining_segments = self.segments.skip(self.current_segment_idx + 1);

        let ty = match resolution {
            TypeNs::TraitId(trait_) => {
                let ty = match remaining_segments.len() {
                    1 => {
                        let trait_ref = self.lower_trait_ref_from_resolved_path(
                            trait_,
                            Ty::new_error(self.ctx.interner, ErrorGuaranteed),
                        );
                        self.skip_resolved_segment();
                        let segment = self.current_or_prev_segment;
                        let trait_id = match trait_ref.def_id {
                            SolverDefId::TraitId(id) => id,
                            _ => unreachable!(),
                        };
                        let found =
                            self.ctx.db.trait_items(trait_id).associated_type_by_name(segment.name);

                        match found {
                            Some(associated_ty) => {
                                // FIXME: `substs_from_path_segment()` pushes `TyKind::Error` for every parent
                                // generic params. It's inefficient to splice the `Substitution`s, so we may want
                                // that method to optionally take parent `Substitution` as we already know them at
                                // this point (`trait_ref.substitution`).
                                let substitution = self.substs_from_path_segment(
                                    associated_ty.into(),
                                    false,
                                    None,
                                );
                                let args = crate::next_solver::GenericArgs::new_from_iter(
                                    self.ctx.interner,
                                    trait_ref
                                        .args
                                        .iter()
                                        .chain(substitution.iter().skip(trait_ref.args.len())),
                                );
                                Ty::new_alias(
                                    self.ctx.interner,
                                    AliasTyKind::Projection,
                                    AliasTy::new_from_args(
                                        self.ctx.interner,
                                        associated_ty.into(),
                                        args,
                                    ),
                                )
                            }
                            None => {
                                // FIXME: report error (associated type not found)
                                Ty::new_error(self.ctx.interner, ErrorGuaranteed)
                            }
                        }
                    }
                    0 => {
                        // Trait object type without dyn; this should be handled in upstream. See
                        // `lower_path()`.
                        stdx::never!("unexpected fully resolved trait path");
                        Ty::new_error(self.ctx.interner, ErrorGuaranteed)
                    }
                    _ => {
                        // FIXME report error (ambiguous associated type)
                        Ty::new_error(self.ctx.interner, ErrorGuaranteed)
                    }
                };
                return (ty, None);
            }
            TypeNs::TraitAliasId(_) => {
                // FIXME(trait_alias): Implement trait alias.
                return (Ty::new_error(self.ctx.interner, ErrorGuaranteed), None);
            }
            TypeNs::GenericParam(param_id) => {
                let generics = self.ctx.generics();
                let idx = generics.type_or_const_param_idx(param_id.into());
                match idx {
                    None => {
                        never!("no matching generics");
                        Ty::new_error(self.ctx.interner, ErrorGuaranteed)
                    }
                    Some(idx) => {
                        let (pidx, param) = generics.iter().nth(idx).unwrap();
                        assert_eq!(pidx, param_id.into());
                        let p = match param {
                            GenericParamDataRef::TypeParamData(p) => p,
                            _ => unreachable!(),
                        };
                        Ty::new_param(
                            self.ctx.interner,
                            idx as u32,
                            p.name
                                .as_ref()
                                .map_or_else(|| sym::MISSING_NAME.clone(), |p| p.symbol().clone()),
                        )
                    }
                }
            }
            TypeNs::SelfType(impl_id) => {
                impl_self_ty_query(self.ctx.db, impl_id).skip_binder()
            }
            TypeNs::AdtSelfType(adt) => {
                let args = crate::next_solver::GenericArgs::identity_for_item(
                    self.ctx.interner,
                    adt.into(),
                );
                Ty::new_adt(self.ctx.interner, AdtDef::new(adt.into(), self.ctx.interner), args)
            }

            TypeNs::AdtId(it) => self.lower_path_inner(it.into(), infer_args),
            TypeNs::BuiltinType(it) => self.lower_path_inner(it.into(), infer_args),
            TypeNs::TypeAliasId(it) => self.lower_path_inner(it.into(), infer_args),
            // FIXME: report error
            TypeNs::EnumVariantId(_) | TypeNs::ModuleId(_) => {
                return (Ty::new_error(self.ctx.interner, ErrorGuaranteed), None);
            }
        };

        self.skip_resolved_segment();
        self.lower_ty_relative_path(ty, Some(resolution))
    }

    fn handle_type_ns_resolution(&mut self, resolution: &TypeNs) {
        let mut prohibit_generics_on_resolved = |reason| {
            if self.current_or_prev_segment.args_and_bindings.is_some() {
                let segment = self.current_segment_u32();
                self.on_diagnostic(PathLoweringDiagnostic::GenericArgsProhibited {
                    segment,
                    reason,
                });
            }
        };

        match resolution {
            TypeNs::SelfType(_) => {
                prohibit_generics_on_resolved(GenericArgsProhibitedReason::SelfTy)
            }
            TypeNs::GenericParam(_) => {
                prohibit_generics_on_resolved(GenericArgsProhibitedReason::TyParam)
            }
            TypeNs::AdtSelfType(_) => {
                prohibit_generics_on_resolved(GenericArgsProhibitedReason::SelfTy)
            }
            TypeNs::BuiltinType(_) => {
                prohibit_generics_on_resolved(GenericArgsProhibitedReason::PrimitiveTy)
            }
            TypeNs::ModuleId(_) => {
                prohibit_generics_on_resolved(GenericArgsProhibitedReason::Module)
            }
            TypeNs::AdtId(_)
            | TypeNs::EnumVariantId(_)
            | TypeNs::TypeAliasId(_)
            | TypeNs::TraitId(_)
            | TypeNs::TraitAliasId(_) => {}
        }
    }

    pub(crate) fn resolve_path_in_type_ns_fully(&mut self) -> Option<TypeNs> {
        let (res, unresolved) = self.resolve_path_in_type_ns()?;
        if unresolved.is_some() {
            return None;
        }
        Some(res)
    }

    pub(crate) fn resolve_path_in_type_ns(&mut self) -> Option<(TypeNs, Option<usize>)> {
        let (resolution, remaining_index, _, prefix_info) =
            self.ctx.resolver.resolve_path_in_type_ns_with_prefix_info(self.ctx.db, self.path)?;

        let segments = self.segments;
        if segments.is_empty() || matches!(self.path, Path::LangItem(..)) {
            // `segments.is_empty()` can occur with `self`.
            return Some((resolution, remaining_index));
        }

        let (module_segments, resolved_segment_idx, enum_segment) = match remaining_index {
            None if prefix_info.enum_variant => {
                (segments.strip_last_two(), segments.len() - 1, Some(segments.len() - 2))
            }
            None => (segments.strip_last(), segments.len() - 1, None),
            Some(i) => (segments.take(i - 1), i - 1, None),
        };

        self.current_segment_idx = resolved_segment_idx;
        self.current_or_prev_segment =
            segments.get(resolved_segment_idx).expect("should have resolved segment");

        if matches!(self.path, Path::BarePath(..)) {
            // Bare paths cannot have generics, so skip them as an optimization.
            return Some((resolution, remaining_index));
        }

        for (i, mod_segment) in module_segments.iter().enumerate() {
            if mod_segment.args_and_bindings.is_some() {
                self.on_diagnostic(PathLoweringDiagnostic::GenericArgsProhibited {
                    segment: i as u32,
                    reason: GenericArgsProhibitedReason::Module,
                });
            }
        }

        if let Some(enum_segment) = enum_segment {
            if segments.get(enum_segment).is_some_and(|it| it.args_and_bindings.is_some())
                && segments.get(enum_segment + 1).is_some_and(|it| it.args_and_bindings.is_some())
            {
                self.on_diagnostic(PathLoweringDiagnostic::GenericArgsProhibited {
                    segment: (enum_segment + 1) as u32,
                    reason: GenericArgsProhibitedReason::EnumVariant,
                });
            }
        }

        self.handle_type_ns_resolution(&resolution);

        Some((resolution, remaining_index))
    }

    pub(crate) fn resolve_path_in_value_ns(
        &mut self,
        hygiene_id: HygieneId,
    ) -> Option<ResolveValueResult> {
        let (res, prefix_info) = self.ctx.resolver.resolve_path_in_value_ns_with_prefix_info(
            self.ctx.db,
            self.path,
            hygiene_id,
        )?;

        let segments = self.segments;
        if segments.is_empty() || matches!(self.path, Path::LangItem(..)) {
            // `segments.is_empty()` can occur with `self`.
            return Some(res);
        }

        let (mod_segments, enum_segment, resolved_segment_idx) = match res {
            ResolveValueResult::Partial(_, unresolved_segment, _) => {
                (segments.take(unresolved_segment - 1), None, unresolved_segment - 1)
            }
            ResolveValueResult::ValueNs(ValueNs::EnumVariantId(_), _)
                if prefix_info.enum_variant =>
            {
                (segments.strip_last_two(), segments.len().checked_sub(2), segments.len() - 1)
            }
            ResolveValueResult::ValueNs(..) => (segments.strip_last(), None, segments.len() - 1),
        };

        self.current_segment_idx = resolved_segment_idx;
        self.current_or_prev_segment =
            segments.get(resolved_segment_idx).expect("should have resolved segment");

        for (i, mod_segment) in mod_segments.iter().enumerate() {
            if mod_segment.args_and_bindings.is_some() {
                self.on_diagnostic(PathLoweringDiagnostic::GenericArgsProhibited {
                    segment: i as u32,
                    reason: GenericArgsProhibitedReason::Module,
                });
            }
        }

        if let Some(enum_segment) = enum_segment {
            if segments.get(enum_segment).is_some_and(|it| it.args_and_bindings.is_some())
                && segments.get(enum_segment + 1).is_some_and(|it| it.args_and_bindings.is_some())
            {
                self.on_diagnostic(PathLoweringDiagnostic::GenericArgsProhibited {
                    segment: (enum_segment + 1) as u32,
                    reason: GenericArgsProhibitedReason::EnumVariant,
                });
            }
        }

        match &res {
            ResolveValueResult::ValueNs(resolution, _) => {
                let resolved_segment_idx = self.current_segment_u32();
                let resolved_segment = self.current_or_prev_segment;

                let mut prohibit_generics_on_resolved = |reason| {
                    if resolved_segment.args_and_bindings.is_some() {
                        self.on_diagnostic(PathLoweringDiagnostic::GenericArgsProhibited {
                            segment: resolved_segment_idx,
                            reason,
                        });
                    }
                };

                match resolution {
                    ValueNs::ImplSelf(_) => {
                        prohibit_generics_on_resolved(GenericArgsProhibitedReason::SelfTy)
                    }
                    // FIXME: rustc generates E0107 (incorrect number of generic arguments) and not
                    // E0109 (generic arguments provided for a type that doesn't accept them) for
                    // consts and statics, presumably as a defense against future in which consts
                    // and statics can be generic, or just because it was easier for rustc implementors.
                    // That means we'll show the wrong error code. Because of us it's easier to do it
                    // this way :)
                    ValueNs::GenericParam(_) | ValueNs::ConstId(_) => {
                        prohibit_generics_on_resolved(GenericArgsProhibitedReason::Const)
                    }
                    ValueNs::StaticId(_) => {
                        prohibit_generics_on_resolved(GenericArgsProhibitedReason::Static)
                    }
                    ValueNs::FunctionId(_) | ValueNs::StructId(_) | ValueNs::EnumVariantId(_) => {}
                    ValueNs::LocalBinding(_) => {}
                }
            }
            ResolveValueResult::Partial(resolution, _, _) => {
                self.handle_type_ns_resolution(resolution);
            }
        };
        Some(res)
    }

    fn select_associated_type(&mut self, res: Option<TypeNs>) -> Ty<'db> {
        let interner = self.ctx.interner;
        let Some(res) = res else {
            return Ty::new_error(self.ctx.interner, ErrorGuaranteed);
        };
        let segment = self.current_or_prev_segment;
        let ty = named_associated_type_shorthand_candidates(
            self.ctx.db,
            self.ctx.resolver.krate(),
            self.ctx.def,
            res,
            Some(segment.name.clone()),
            move |name, t, associated_ty| {
                if name != segment.name {
                    return None;
                }

                // FIXME: `substs_from_path_segment()` pushes `TyKind::Error` for every parent
                // generic params. It's inefficient to splice the `Substitution`s, so we may want
                // that method to optionally take parent `Substitution` as we already know them at
                // this point (`t.substitution`).
                let substs = self.substs_from_path_segment(associated_ty.into(), false, None);

                let substs = crate::next_solver::GenericArgs::new_from_iter(
                    interner,
                    t.args.iter().chain(substs.iter().skip(t.args.len())),
                );

                Some(Ty::new_alias(
                    self.ctx.interner,
                    AliasTyKind::Projection,
                    AliasTy::new(self.ctx.interner, associated_ty.into(), substs),
                ))
            },
        );

        ty.unwrap_or_else(|| Ty::new_error(interner, ErrorGuaranteed))
    }

    fn lower_path_inner(&mut self, typeable: TyDefId, infer_args: bool) -> Ty<'db> {
        let generic_def = match typeable {
            TyDefId::BuiltinType(builtinty) => return builtin(self.ctx.interner, builtinty),
            TyDefId::AdtId(it) => it.into(),
            TyDefId::TypeAliasId(it) => it.into(),
        };
        let args = self.substs_from_path_segment(generic_def, infer_args, None);
        let ty = ty_query(self.ctx.db, typeable);
        ty.instantiate(self.ctx.interner, args)
    }

    /// Collect generic arguments from a path into a `Substs`. See also
    /// `create_substs_for_ast_path` and `def_to_ty` in rustc.
    pub(crate) fn substs_from_path(
        &mut self,
        // Note that we don't call `db.value_type(resolved)` here,
        // `ValueTyDefId` is just a convenient way to pass generics and
        // special-case enum variants
        resolved: ValueTyDefId,
        infer_args: bool,
    ) -> crate::next_solver::GenericArgs<'db> {
        let interner = self.ctx.interner;
        let prev_current_segment_idx = self.current_segment_idx;
        let prev_current_segment = self.current_or_prev_segment;

        let generic_def = match resolved {
            ValueTyDefId::FunctionId(it) => it.into(),
            ValueTyDefId::StructId(it) => it.into(),
            ValueTyDefId::UnionId(it) => it.into(),
            ValueTyDefId::ConstId(it) => it.into(),
            ValueTyDefId::StaticId(_) => {
                return crate::next_solver::GenericArgs::new_from_iter(interner, []);
            }
            ValueTyDefId::EnumVariantId(var) => {
                // the generic args for an enum variant may be either specified
                // on the segment referring to the enum, or on the segment
                // referring to the variant. So `Option::<T>::None` and
                // `Option::None::<T>` are both allowed (though the former is
                // FIXME: This isn't strictly correct, enum variants may be used not through the enum
                // (via `use Enum::Variant`). The resolver returns whether they were, but we don't have its result
                // available here. The worst that can happen is that we will show some confusing diagnostics to the user,
                // if generics exist on the module and they don't match with the variant.
                // preferred). See also `def_ids_for_path_segments` in rustc.
                //
                // `wrapping_sub(1)` will return a number which `get` will return None for if current_segment_idx<2.
                // This simplifies the code a bit.
                let penultimate_idx = self.current_segment_idx.wrapping_sub(1);
                let penultimate = self.segments.get(penultimate_idx);
                if let Some(penultimate) = penultimate {
                    if self.current_or_prev_segment.args_and_bindings.is_none()
                        && penultimate.args_and_bindings.is_some()
                    {
                        self.current_segment_idx = penultimate_idx;
                        self.current_or_prev_segment = penultimate;
                    }
                }
                var.lookup(self.ctx.db).parent.into()
            }
        };
        let result = self.substs_from_path_segment(generic_def, infer_args, None);
        self.current_segment_idx = prev_current_segment_idx;
        self.current_or_prev_segment = prev_current_segment;
        result
    }

    pub(crate) fn substs_from_path_segment(
        &mut self,
        def: GenericDefId,
        infer_args: bool,
        explicit_self_ty: Option<Ty<'db>>,
    ) -> crate::next_solver::GenericArgs<'db> {
        let prohibit_parens = match def {
            GenericDefId::TraitId(trait_) => {
                // RTN is prohibited anyways if we got here.
                let is_rtn =
                    self.current_or_prev_segment.args_and_bindings.is_some_and(|generics| {
                        generics.parenthesized == GenericArgsParentheses::ReturnTypeNotation
                    });
                let is_fn_trait = !self
                    .ctx
                    .db
                    .trait_signature(trait_)
                    .flags
                    .contains(TraitFlags::RUSTC_PAREN_SUGAR);
                is_rtn || is_fn_trait
            }
            _ => true,
        };
        if prohibit_parens && self.prohibit_parenthesized_generic_args() {
            return unknown_subst(self.ctx.interner, def);
        }

        self.substs_from_args_and_bindings(
            self.current_or_prev_segment.args_and_bindings,
            def,
            infer_args,
            explicit_self_ty,
        )
    }

    pub(super) fn substs_from_args_and_bindings(
        &mut self,
        args_and_bindings: Option<&GenericArgs>,
        def: GenericDefId,
        infer_args: bool,
        explicit_self_ty: Option<Ty<'db>>,
    ) -> crate::next_solver::GenericArgs<'db> {
        let interner = self.ctx.interner;
        // Order is
        // - Optional Self parameter
        // - Lifetime parameters
        // - Type or Const parameters
        // - Parent parameters
        let def_generics = generics(self.ctx.db, def);
        let (
            parent_params,
            self_param,
            type_params,
            const_params,
            impl_trait_params,
            lifetime_params,
        ) = def_generics.provenance_split();
        let item_len =
            self_param as usize + type_params + const_params + impl_trait_params + lifetime_params;
        let total_len = parent_params + item_len;

        let mut substs = Vec::new();

        // we need to iterate the lifetime and type/const params separately as our order of them
        // differs from the supplied syntax

        let ty_error = || Ty::new_error(self.ctx.interner, ErrorGuaranteed);
        let mut def_toc_iter = def_generics.iter_self_type_or_consts_id();
        let mut fill_self_param = || {
            if self_param {
                let self_ty = explicit_self_ty.map(|x| x.into()).unwrap_or_else(ty_error);

                if let Some(id) = def_toc_iter.next() {
                    assert!(matches!(id, GenericParamId::TypeParamId(_)));
                    substs.push(self_ty.into());
                }
            }
        };
        let mut had_explicit_args = false;

        if let Some(&GenericArgs { ref args, has_self_type, .. }) = args_and_bindings {
            // Fill in the self param first
            if has_self_type && self_param {
                had_explicit_args = true;
                if let Some(id) = def_toc_iter.next() {
                    assert!(matches!(id, GenericParamId::TypeParamId(_)));
                    had_explicit_args = true;
                    if let GenericArg::Type(ty) = &args[0] {
                        substs.push(self.ctx.lower_ty(*ty).into());
                    }
                }
            } else {
                fill_self_param()
            };

            // Then fill in the supplied lifetime args, or error lifetimes if there are too few
            // (default lifetimes aren't a thing)
            for arg in args
                .iter()
                .filter_map(|arg| match arg {
                    GenericArg::Lifetime(arg) => Some(self.ctx.lower_lifetime(arg)),
                    _ => None,
                })
                .chain(iter::repeat_with(|| Region::error(interner)))
                .take(lifetime_params)
            {
                substs.push(arg.into());
            }

            let skip = if has_self_type { 1 } else { 0 };
            // Fill in supplied type and const args
            // Note if non-lifetime args are provided, it should be all of them, but we can't rely on that
            for (arg, id) in args
                .iter()
                .filter(|arg| !matches!(arg, GenericArg::Lifetime(_)))
                .skip(skip)
                .take(type_params + const_params)
                .zip(def_toc_iter)
            {
                had_explicit_args = true;
                let arg = lower_generic_arg(
                    self.ctx.db,
                    id,
                    arg,
                    self.ctx,
                    self.ctx.store,
                    |this, type_ref| this.lower_ty(type_ref),
                    |this, const_ref, ty| this.lower_const(const_ref, ty),
                    |ctx, path, ty| ctx.lower_path_as_const(path, ty),
                    |this, lifetime_ref| this.lower_lifetime(lifetime_ref),
                );
                substs.push(arg);
            }
        } else {
            fill_self_param();
        }

        let param_to_err = |id| match id {
            GenericParamId::ConstParamId(x) => {
                unknown_const(self.ctx.db.const_param_ty(x).to_nextsolver(self.ctx.interner)).into()
            }
            GenericParamId::TypeParamId(_) => {
                Ty::new_error(self.ctx.interner, ErrorGuaranteed).into()
            }
            GenericParamId::LifetimeParamId(_) => Region::error(interner).into(),
        };
        // handle defaults. In expression or pattern path segments without
        // explicitly specified type arguments, missing type arguments are inferred
        // (i.e. defaults aren't used).
        // Generic parameters for associated types are not supposed to have defaults, so we just
        // ignore them.
        let is_assoc_ty = || match def {
            GenericDefId::TypeAliasId(id) => {
                matches!(id.lookup(self.ctx.db).container, ItemContainerId::TraitId(_))
            }
            _ => false,
        };
        let fill_defaults = (!infer_args || had_explicit_args) && !is_assoc_ty();
        if fill_defaults {
            let defaults = &*self.ctx.db.generic_defaults(def);
            let (item, _parent) = defaults.split_at(item_len);
            let parent_from = item_len - substs.len();

            let mut rem =
                def_generics.iter_id().skip(substs.len()).map(param_to_err).collect::<Vec<_>>();
            // Fill in defaults for type/const params
            for (idx, default_ty) in item[substs.len()..].iter().enumerate() {
                // each default can depend on the previous parameters
                let substs_so_far = crate::next_solver::GenericArgs::new_from_iter(
                    interner,
                    substs.iter().cloned().chain(rem[idx..].iter().cloned()),
                );
                substs.push(apply_args_to_binder(
                    default_ty.to_nextsolver(self.ctx.interner),
                    substs_so_far,
                    DbInterner::new(),
                ));
            }
            // Fill in remaining parent params
            substs.extend(rem.drain(parent_from..));
        } else {
            // Fill in remaining def params and parent params
            substs.extend(def_generics.iter_id().skip(substs.len()).map(param_to_err));
        }

        assert_eq!(substs.len(), total_len, "expected {} substs, got {}", total_len, substs.len());
        crate::next_solver::GenericArgs::new_from_iter(interner, substs)
    }

    pub(crate) fn lower_trait_ref_from_resolved_path(
        &mut self,
        resolved: TraitId,
        explicit_self_ty: Ty<'db>,
    ) -> TraitRef<'db> {
        let args = self.trait_ref_substs_from_path(resolved, explicit_self_ty);
        TraitRef::new_from_args(self.ctx.interner, resolved.into(), args)
    }

    fn trait_ref_substs_from_path(
        &mut self,
        resolved: TraitId,
        explicit_self_ty: Ty<'db>,
    ) -> crate::next_solver::GenericArgs<'db> {
        self.substs_from_path_segment(resolved.into(), false, Some(explicit_self_ty))
    }

    pub(super) fn assoc_type_bindings_from_type_bound<'c>(
        mut self,
        trait_ref: TraitRef<'db>,
    ) -> Option<impl Iterator<Item = Clause<'db>> + use<'a, 'b, 'c, 'db>> {
        let interner = self.ctx.interner;
        self.current_or_prev_segment.args_and_bindings.map(|args_and_bindings| {
            args_and_bindings.bindings.iter().flat_map(move |binding| {
                let found = associated_type_by_name_including_super_traits(
                    self.ctx.db,
                    trait_ref.clone(),
                    &binding.name,
                );
                let (super_trait_ref, associated_ty) = match found {
                    None => return SmallVec::new(),
                    Some(t) => t,
                };
                // FIXME: `substs_from_path_segment()` pushes `TyKind::Error` for every parent
                // generic params. It's inefficient to splice the `Substitution`s, so we may want
                // that method to optionally take parent `Substitution` as we already know them at
                // this point (`super_trait_ref.substitution`).
                let args = self.substs_from_args_and_bindings(
                    binding.args.as_ref(),
                    associated_ty.into(),
                    false, // this is not relevant
                    Some(super_trait_ref.self_ty()),
                );
                let args = crate::next_solver::GenericArgs::new_from_iter(
                    interner,
                    super_trait_ref.args.iter().chain(args.iter().skip(super_trait_ref.args.len())),
                );
                let projection_term =
                    AliasTerm::new_from_args(interner, associated_ty.into(), args.clone());
                let mut predicates: SmallVec<[_; 1]> = SmallVec::with_capacity(
                    binding.type_ref.as_ref().map_or(0, |_| 1) + binding.bounds.len(),
                );
                if let Some(type_ref) = binding.type_ref {
                    match (&self.ctx.store[type_ref], self.ctx.impl_trait_mode.mode) {
                        (TypeRef::ImplTrait(_), ImplTraitLoweringMode::Disallowed) => (),
                        (_, ImplTraitLoweringMode::Disallowed | ImplTraitLoweringMode::Opaque) => {
                            let ty = self.ctx.lower_ty(type_ref);
                            let pred = Clause(Predicate::new(
                                interner,
                                Binder::dummy(rustc_type_ir::PredicateKind::Clause(
                                    rustc_type_ir::ClauseKind::Projection(ProjectionPredicate {
                                        projection_term,
                                        term: ty.into(),
                                    }),
                                )),
                            ));
                            predicates.push(pred);
                        }
                    }
                }
                for bound in binding.bounds.iter() {
                    predicates.extend(self.ctx.lower_type_bound(
                        bound,
                        Ty::new_alias(
                            self.ctx.interner,
                            AliasTyKind::Projection,
                            AliasTy::new_from_args(
                                self.ctx.interner,
                                associated_ty.into(),
                                args.clone(),
                            ),
                        ),
                        false,
                    ));
                }
                predicates
            })
        })
    }
}

fn unknown_subst<'db>(
    interner: DbInterner<'db>,
    def: impl Into<GenericDefId>,
) -> crate::next_solver::GenericArgs<'db> {
    let params = generics(interner.db(), def.into());
    crate::next_solver::GenericArgs::new_from_iter(
        interner,
        params.iter_id().map(|id| match id {
            GenericParamId::TypeParamId(_) => Ty::new_error(interner, ErrorGuaranteed).into(),
            GenericParamId::ConstParamId(id) => {
                unknown_const_as_generic(const_param_ty_query(interner.db(), id)).into()
            }
            GenericParamId::LifetimeParamId(_) => {
                crate::next_solver::Region::error(interner).into()
            }
        }),
    )
}

pub fn builtin<'db>(interner: DbInterner<'db>, builtin: BuiltinType) -> Ty<'db> {
    match builtin {
        BuiltinType::Char => Ty::new(interner, rustc_type_ir::TyKind::Char),
        BuiltinType::Bool => Ty::new_bool(interner),
        BuiltinType::Str => Ty::new(interner, rustc_type_ir::TyKind::Str),
        BuiltinType::Int(t) => {
            let int_ty = match primitive::int_ty_from_builtin(t) {
                chalk_ir::IntTy::Isize => rustc_type_ir::IntTy::Isize,
                chalk_ir::IntTy::I8 => rustc_type_ir::IntTy::I8,
                chalk_ir::IntTy::I16 => rustc_type_ir::IntTy::I16,
                chalk_ir::IntTy::I32 => rustc_type_ir::IntTy::I32,
                chalk_ir::IntTy::I64 => rustc_type_ir::IntTy::I64,
                chalk_ir::IntTy::I128 => rustc_type_ir::IntTy::I128,
            };
            Ty::new_int(interner, int_ty)
        }
        BuiltinType::Uint(t) => {
            let uint_ty = match primitive::uint_ty_from_builtin(t) {
                chalk_ir::UintTy::Usize => rustc_type_ir::UintTy::Usize,
                chalk_ir::UintTy::U8 => rustc_type_ir::UintTy::U8,
                chalk_ir::UintTy::U16 => rustc_type_ir::UintTy::U16,
                chalk_ir::UintTy::U32 => rustc_type_ir::UintTy::U32,
                chalk_ir::UintTy::U64 => rustc_type_ir::UintTy::U64,
                chalk_ir::UintTy::U128 => rustc_type_ir::UintTy::U128,
            };
            Ty::new_uint(interner, uint_ty)
        }
        BuiltinType::Float(t) => {
            let float_ty = match primitive::float_ty_from_builtin(t) {
                chalk_ir::FloatTy::F16 => rustc_type_ir::FloatTy::F16,
                chalk_ir::FloatTy::F32 => rustc_type_ir::FloatTy::F32,
                chalk_ir::FloatTy::F64 => rustc_type_ir::FloatTy::F64,
                chalk_ir::FloatTy::F128 => rustc_type_ir::FloatTy::F128,
            };
            Ty::new_float(interner, float_ty)
        }
    }
}
