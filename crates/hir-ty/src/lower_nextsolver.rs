//! Methods for lowering the HIR to types. There are two main cases here:
//!
//!  - Lowering a type reference like `&usize` or `Option<foo::bar::Baz>` to a
//!    type: The entry point for this is `TyLoweringContext::lower_ty`.
//!  - Building the type for an item: This happens through the `ty` query.
//!
//! This usually involves resolving names, collecting generic arguments etc.
pub(crate) mod path;

use std::{
    cell::OnceCell,
    collections::HashSet,
    iter, mem,
    ops::{self, Not as _},
};

use base_db::Crate;
use either::Either;
use hir_def::{
    AdtId, AssocItemId, CallableDefId, ConstParamId, EnumVariantId, FunctionId, GenericDefId,
    GenericParamId, ImplId, LocalFieldId, Lookup, StructId, TypeAliasId, TypeOrConstParamId,
    VariantId,
    expr_store::{
        ExpressionStore,
        path::{GenericArg, Path},
    },
    hir::generics::{TypeOrConstParamData, WherePredicate, WherePredicateTypeTarget},
    lang_item::LangItem,
    resolver::{HasResolver, LifetimeNs, Resolver, TypeNs},
    signatures::{TraitFlags, TypeAliasFlags},
    type_ref::{
        ConstRef, LifetimeRef, LiteralConstRef, PathId, TraitBoundModifier,
        TraitRef as HirTraitRef, TypeBound, TypeRef, TypeRefId,
    },
};
use hir_expand::name::Name;
use intern::sym;
use la_arena::{Arena, ArenaMap, Idx};
use path::{PathDiagnosticCallback, PathLoweringContext, builtin};
use rustc_ast_ir::Mutability;
use rustc_hash::FxHashSet;
use rustc_pattern_analysis::Captures;
use rustc_type_ir::{
    AliasTyKind, ConstKind, DebruijnIndex, ExistentialPredicate, ExistentialProjection,
    ExistentialTraitRef, FnSig, OutlivesPredicate,
    TyKind::{self},
    TypeVisitableExt,
    inherent::{GenericArg as _, GenericArgs as _, IntoKind as _, Region as _, SliceLike, Ty as _},
};
use salsa::plumbing::AsId;
use stdx::never;
use triomphe::Arc;

use crate::{
    FnAbi, ImplTraitId, ParamKind, TyDefId, TyLoweringDiagnostic, TyLoweringDiagnosticKind,
    consteval_nextsolver::{intern_const_ref, path_to_const, unknown_const_as_generic},
    db::HirDatabase,
    generics::{Generics, generics, trait_self_param_idx},
    lower::{Diagnostics, PathDiagnosticCallbackData, create_diagnostics},
    next_solver::{
        AdtDef, AliasTy, Binder, BoundExistentialPredicates, BoundRegionKind, BoundTyKind,
        BoundVarKind, BoundVarKinds, Clause, Const, DbInterner, EarlyBinder, EarlyParamRegion,
        ErrorGuaranteed, GenericArgs, PolyFnSig, Predicate, Region, SolverDefId, TraitPredicate,
        TraitRef, Ty, Tys, abi::Safety, mapping::ChalkToNextSolver,
    },
};

#[derive(PartialEq, Eq, Debug, Hash)]
pub struct ImplTraits<'db> {
    pub(crate) impl_traits: Arena<ImplTrait<'db>>,
}

#[derive(PartialEq, Eq, Debug, Hash)]
pub struct ImplTrait<'db> {
    pub(crate) predicates: Vec<Clause<'db>>,
}

pub type ImplTraitIdx<'db> = Idx<ImplTrait<'db>>;

#[derive(Debug, Default)]
struct ImplTraitLoweringState<'db> {
    /// When turning `impl Trait` into opaque types, we have to collect the
    /// bounds at the same time to get the IDs correct (without becoming too
    /// complicated).
    mode: ImplTraitLoweringMode,
    // This is structured as a struct with fields and not as an enum because it helps with the borrow checker.
    opaque_type_data: Arena<ImplTrait<'db>>,
    param_and_variable_counter: u16,
}
impl<'db> ImplTraitLoweringState<'db> {
    fn new(mode: ImplTraitLoweringMode) -> ImplTraitLoweringState<'db> {
        Self { mode, opaque_type_data: Arena::new(), param_and_variable_counter: 0 }
    }
}

#[derive(Debug)]
pub struct TyLoweringContext<'db: 'a, 'a> {
    pub db: &'db dyn HirDatabase,
    interner: DbInterner<'db>,
    resolver: &'a Resolver,
    store: &'a ExpressionStore,
    def: GenericDefId,
    generics: OnceCell<Generics>,
    in_binders: DebruijnIndex,
    impl_trait_mode: ImplTraitLoweringState<'db>,
    /// Tracks types with explicit `?Sized` bounds.
    pub(crate) unsized_types: FxHashSet<Ty<'db>>,
    pub(crate) diagnostics: Vec<TyLoweringDiagnostic>,
}

impl<'db: 'a, 'a> TyLoweringContext<'db, 'a> {
    pub fn new(
        db: &'db dyn HirDatabase,
        resolver: &'a Resolver,
        store: &'a ExpressionStore,
        def: GenericDefId,
    ) -> Self {
        let impl_trait_mode = ImplTraitLoweringState::new(ImplTraitLoweringMode::Disallowed);
        let in_binders = DebruijnIndex::ZERO;
        Self {
            db,
            interner: DbInterner::new_with(db, Some(resolver.krate()), None),
            resolver,
            def,
            generics: Default::default(),
            store,
            in_binders,
            impl_trait_mode,
            unsized_types: FxHashSet::default(),
            diagnostics: Vec::new(),
        }
    }

    pub fn with_debruijn<T>(
        &mut self,
        debruijn: DebruijnIndex,
        f: impl FnOnce(&mut TyLoweringContext<'db, '_>) -> T,
    ) -> T {
        let old_debruijn = mem::replace(&mut self.in_binders, debruijn);
        let result = f(self);
        self.in_binders = old_debruijn;
        result
    }

    pub fn with_shifted_in<T>(
        &mut self,
        debruijn: DebruijnIndex,
        f: impl FnOnce(&mut TyLoweringContext<'db, '_>) -> T,
    ) -> T {
        self.with_debruijn(self.in_binders.shifted_in(debruijn.as_u32()), f)
    }

    pub fn with_impl_trait_mode(self, impl_trait_mode: ImplTraitLoweringMode) -> Self {
        Self { impl_trait_mode: ImplTraitLoweringState::new(impl_trait_mode), ..self }
    }

    pub fn impl_trait_mode(&mut self, impl_trait_mode: ImplTraitLoweringMode) -> &mut Self {
        self.impl_trait_mode = ImplTraitLoweringState::new(impl_trait_mode);
        self
    }

    pub fn push_diagnostic(&mut self, type_ref: TypeRefId, kind: TyLoweringDiagnosticKind) {
        self.diagnostics.push(TyLoweringDiagnostic { source: type_ref, kind });
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum ImplTraitLoweringMode {
    /// `impl Trait` gets lowered into an opaque type that doesn't unify with
    /// anything except itself. This is used in places where values flow 'out',
    /// i.e. for arguments of the function we're currently checking, and return
    /// types of functions we're calling.
    Opaque,
    /// `impl Trait` is disallowed and will be an error.
    #[default]
    Disallowed,
}

impl<'db, 'a> TyLoweringContext<'db, 'a> {
    pub fn lower_ty(&mut self, type_ref: TypeRefId) -> Ty<'db> {
        self.lower_ty_ext(type_ref).0
    }

    pub fn lower_const(&mut self, const_ref: &ConstRef, const_type: Ty<'db>) -> Const<'db> {
        let const_ref = &self.store[const_ref.expr];
        match const_ref {
            hir_def::hir::Expr::Path(path) => {
                path_to_const(self.db, self.resolver, path, || self.generics(), const_type.clone())
                    .unwrap_or_else(|| unknown_const(const_type))
            }
            hir_def::hir::Expr::Literal(literal) => intern_const_ref(
                self.db,
                &match *literal {
                    hir_def::hir::Literal::Float(_, _)
                    | hir_def::hir::Literal::String(_)
                    | hir_def::hir::Literal::ByteString(_)
                    | hir_def::hir::Literal::CString(_) => LiteralConstRef::Unknown,
                    hir_def::hir::Literal::Char(c) => LiteralConstRef::Char(c),
                    hir_def::hir::Literal::Bool(b) => LiteralConstRef::Bool(b),
                    hir_def::hir::Literal::Int(val, _) => LiteralConstRef::Int(val),
                    hir_def::hir::Literal::Uint(val, _) => LiteralConstRef::UInt(val),
                },
                const_type,
                self.resolver.krate(),
            ),
            _ => unknown_const(const_type),
        }
    }

    pub fn lower_path_as_const(&mut self, path: &Path, const_type: Ty<'db>) -> Const<'db> {
        path_to_const(self.db, self.resolver, path, || self.generics(), const_type.clone())
            .unwrap_or_else(|| unknown_const(const_type))
    }

    fn generics(&self) -> &Generics {
        self.generics.get_or_init(|| generics(self.db, self.def))
    }

    #[tracing::instrument(skip(self), ret)]
    pub fn lower_ty_ext(&mut self, type_ref_id: TypeRefId) -> (Ty<'db>, Option<TypeNs>) {
        let interner = self.interner;
        let mut res = None;
        let type_ref = &self.store[type_ref_id];
        tracing::debug!(?type_ref);
        let ty = match type_ref {
            TypeRef::Never => Ty::new(interner, TyKind::Never),
            TypeRef::Tuple(inner) => {
                let inner_tys = inner.iter().map(|&tr| self.lower_ty(tr));
                Ty::new_tup_from_iter(interner, inner_tys)
            }
            TypeRef::Path(path) => {
                let (ty, res_) =
                    self.lower_path(path, PathId::from_type_ref_unchecked(type_ref_id));
                res = res_;
                ty
            }
            &TypeRef::TypeParam(type_param_id) => {
                res = Some(TypeNs::GenericParam(type_param_id));

                let generics = self.generics();
                let (idx, data) =
                    generics.type_or_const_param(type_param_id.into()).expect("matching generics");
                let type_data = match data {
                    TypeOrConstParamData::TypeParamData(ty) => ty,
                    _ => unreachable!(),
                };
                Ty::new_param(
                    self.interner,
                    idx as u32,
                    type_data
                        .name
                        .as_ref()
                        .map_or_else(|| sym::MISSING_NAME.clone(), |d| d.symbol().clone()),
                )
            }
            &TypeRef::RawPtr(inner, mutability) => {
                let inner_ty = self.lower_ty(inner);
                Ty::new(interner, TyKind::RawPtr(inner_ty, lower_mutability(mutability)))
            }
            TypeRef::Array(array) => {
                let inner_ty = self.lower_ty(array.ty);
                let const_len = self.lower_const(&array.len, Ty::new_usize(interner));
                Ty::new_array_with_const_len(interner, inner_ty, const_len)
            }
            &TypeRef::Slice(inner) => {
                let inner_ty = self.lower_ty(inner);
                Ty::new_slice(interner, inner_ty)
            }
            TypeRef::Reference(ref_) => {
                let inner_ty = self.lower_ty(ref_.ty);
                // FIXME: It should infer the eldided lifetimes instead of stubbing with error
                let lifetime = ref_
                    .lifetime
                    .as_ref()
                    .map_or_else(|| Region::error(interner), |lr| self.lower_lifetime(lr));
                Ty::new_ref(interner, lifetime, inner_ty, lower_mutability(ref_.mutability))
            }
            TypeRef::Placeholder => Ty::new_error(interner, ErrorGuaranteed),
            TypeRef::Fn(fn_) => {
                let substs = self.with_shifted_in(
                    DebruijnIndex::from_u32(1),
                    |ctx: &mut TyLoweringContext<'_, '_>| {
                        Tys::new_from_iter(
                            interner,
                            fn_.params.iter().map(|&(_, tr)| ctx.lower_ty(tr)),
                        )
                    },
                );
                Ty::new_fn_ptr(
                    interner,
                    Binder::dummy(FnSig {
                        abi: fn_.abi.as_ref().map_or(FnAbi::Rust, FnAbi::from_symbol),
                        safety: if fn_.is_unsafe { Safety::Unsafe } else { Safety::Safe },
                        c_variadic: fn_.is_varargs,
                        inputs_and_output: substs,
                    }),
                )
            }
            TypeRef::DynTrait(bounds) => self.lower_dyn_trait(bounds),
            TypeRef::ImplTrait(bounds) => {
                match self.impl_trait_mode.mode {
                    ImplTraitLoweringMode::Opaque => {
                        let origin = match self.resolver.generic_def() {
                            Some(GenericDefId::FunctionId(it)) => Either::Left(it),
                            Some(GenericDefId::TypeAliasId(it)) => Either::Right(it),
                            _ => panic!(
                                "opaque impl trait lowering must be in function or type alias"
                            ),
                        };

                        // this dance is to make sure the data is in the right
                        // place even if we encounter more opaque types while
                        // lowering the bounds
                        let idx = self
                            .impl_trait_mode
                            .opaque_type_data
                            .alloc(ImplTrait { predicates: Vec::default() });

                        // FIXME(next-solver): this from_raw/into_raw dance isn't nice, but it's minimal
                        let impl_trait_id = origin.either(
                            |f| ImplTraitId::ReturnTypeImplTrait(f, Idx::from_raw(idx.into_raw())),
                            |a| ImplTraitId::TypeAliasImplTrait(a, Idx::from_raw(idx.into_raw())),
                        );
                        let opaque_ty_id: SolverDefId =
                            self.db.intern_impl_trait_id(impl_trait_id).into();

                        // We don't want to lower the bounds inside the binders
                        // we're currently in, because they don't end up inside
                        // those binders. E.g. when we have `impl Trait<impl
                        // OtherTrait<T>>`, the `impl OtherTrait<T>` can't refer
                        // to the self parameter from `impl Trait`, and the
                        // bounds aren't actually stored nested within each
                        // other, but separately. So if the `T` refers to a type
                        // parameter of the outer function, it's just one binder
                        // away instead of two.
                        let actual_opaque_type_data =
                            self.with_debruijn(DebruijnIndex::ZERO, |ctx| {
                                ctx.lower_impl_trait(
                                    opaque_ty_id.into(),
                                    bounds,
                                    self.resolver.krate(),
                                )
                            });
                        self.impl_trait_mode.opaque_type_data[idx] = actual_opaque_type_data;

                        let args = GenericArgs::identity_for_item(self.interner, opaque_ty_id);
                        Ty::new_alias(
                            self.interner,
                            AliasTyKind::Opaque,
                            AliasTy::new_from_args(self.interner, opaque_ty_id, args),
                        )
                    }
                    ImplTraitLoweringMode::Disallowed => {
                        // FIXME: report error
                        Ty::new_error(self.interner, ErrorGuaranteed)
                    }
                }
            }
            TypeRef::Error => Ty::new_error(self.interner, ErrorGuaranteed),
        };
        (ty, res)
    }

    /// This is only for `generic_predicates_for_param`, where we can't just
    /// lower the self types of the predicates since that could lead to cycles.
    /// So we just check here if the `type_ref` resolves to a generic param, and which.
    fn lower_ty_only_param(&self, type_ref: TypeRefId) -> Option<TypeOrConstParamId> {
        let type_ref = &self.store[type_ref];
        let path = match type_ref {
            TypeRef::Path(path) => path,
            &TypeRef::TypeParam(idx) => return Some(idx.into()),
            _ => return None,
        };
        if path.type_anchor().is_some() {
            return None;
        }
        if path.segments().len() > 1 {
            return None;
        }
        let resolution = match self.resolver.resolve_path_in_type_ns(self.db, path) {
            Some((it, None, _)) => it,
            _ => return None,
        };
        match resolution {
            TypeNs::GenericParam(param_id) => Some(param_id.into()),
            _ => None,
        }
    }

    #[inline]
    fn on_path_diagnostic_callback(type_ref: TypeRefId) -> PathDiagnosticCallback<'static, 'db> {
        PathDiagnosticCallback {
            data: Either::Left(PathDiagnosticCallbackData(type_ref)),
            callback: |data, this, diag| {
                let type_ref = data.as_ref().left().unwrap().0;
                this.push_diagnostic(type_ref, TyLoweringDiagnosticKind::PathDiagnostic(diag))
            },
        }
    }

    #[inline]
    fn at_path(&mut self, path_id: PathId) -> PathLoweringContext<'_, 'a, 'db> {
        PathLoweringContext::new(
            self,
            Self::on_path_diagnostic_callback(path_id.type_ref()),
            &self.store[path_id],
        )
    }

    pub(crate) fn lower_path(&mut self, path: &Path, path_id: PathId) -> (Ty<'db>, Option<TypeNs>) {
        // Resolve the path (in type namespace)
        if let Some(type_ref) = path.type_anchor() {
            let (ty, res) = self.lower_ty_ext(type_ref);
            let mut ctx = self.at_path(path_id);
            return ctx.lower_ty_relative_path(ty, res);
        }

        let mut ctx = self.at_path(path_id);
        let (resolution, remaining_index) = match ctx.resolve_path_in_type_ns() {
            Some(it) => it,
            None => return (Ty::new_error(self.interner, ErrorGuaranteed), None),
        };

        if matches!(resolution, TypeNs::TraitId(_)) && remaining_index.is_none() {
            // trait object type without dyn
            let bound = TypeBound::Path(path_id, TraitBoundModifier::None);
            let ty = self.lower_dyn_trait(&[bound]);
            return (ty, None);
        }

        ctx.lower_partly_resolved_path(resolution, false)
    }

    fn lower_trait_ref_from_path(
        &mut self,
        path_id: PathId,
        explicit_self_ty: Ty<'db>,
    ) -> Option<(TraitRef<'db>, PathLoweringContext<'_, 'a, 'db>)> {
        let mut ctx = self.at_path(path_id);
        let resolved = match ctx.resolve_path_in_type_ns_fully()? {
            // FIXME(trait_alias): We need to handle trait alias here.
            TypeNs::TraitId(tr) => tr,
            _ => return None,
        };
        Some((ctx.lower_trait_ref_from_resolved_path(resolved, explicit_self_ty), ctx))
    }

    fn lower_trait_ref(
        &mut self,
        trait_ref: &HirTraitRef,
        explicit_self_ty: Ty<'db>,
    ) -> Option<TraitRef<'db>> {
        self.lower_trait_ref_from_path(trait_ref.path, explicit_self_ty).map(|it| it.0)
    }

    pub(crate) fn lower_where_predicate<'b>(
        &'b mut self,
        where_predicate: &'b WherePredicate,
        generics: &'b Generics,
        predicate_owner: GenericDefId,
        ignore_bindings: bool,
    ) -> impl Iterator<Item = Clause<'db>> + use<'a, 'b, 'db> {
        match where_predicate {
            WherePredicate::ForLifetime { target, bound, .. }
            | WherePredicate::TypeBound { target, bound } => {
                let self_ty = match target {
                    WherePredicateTypeTarget::TypeRef(type_ref) => self.lower_ty(*type_ref),
                    &WherePredicateTypeTarget::TypeOrConstParam(local_id) => {
                        let param_id =
                            hir_def::TypeOrConstParamId { parent: predicate_owner, local_id };
                        let (idx, data) =
                            generics.type_or_const_param(param_id).expect("matching generics");
                        let type_data = match data {
                            TypeOrConstParamData::TypeParamData(ty) => ty,
                            _ => unreachable!(),
                        };
                        Ty::new_param(
                            self.interner,
                            idx as u32,
                            type_data
                                .name
                                .as_ref()
                                .map_or_else(|| sym::MISSING_NAME.clone(), |d| d.symbol().clone()),
                        )
                    }
                };
                Either::Left(self.lower_type_bound(bound, self_ty, ignore_bindings))
            }
            WherePredicate::Lifetime { bound, target } => {
                Either::Right(iter::once(Clause(Predicate::new(
                    self.interner,
                    Binder::dummy(rustc_type_ir::PredicateKind::Clause(
                        rustc_type_ir::ClauseKind::RegionOutlives(OutlivesPredicate(
                            self.lower_lifetime(bound),
                            self.lower_lifetime(target),
                        )),
                    )),
                ))))
            }
        }
        .into_iter()
    }

    pub(crate) fn lower_type_bound<'b>(
        &'b mut self,
        bound: &'b TypeBound,
        self_ty: Ty<'db>,
        ignore_bindings: bool,
    ) -> impl Iterator<Item = Clause<'db>> + use<'b, 'a, 'db> {
        let interner = self.interner;
        let mut assoc_bounds = None;
        let mut clause = None;
        match bound {
            &TypeBound::Path(path, TraitBoundModifier::None) | &TypeBound::ForLifetime(_, path) => {
                // FIXME Don't silently drop the hrtb lifetimes here
                if let Some((trait_ref, ctx)) = self.lower_trait_ref_from_path(path, self_ty) {
                    if !ignore_bindings {
                        assoc_bounds = ctx.assoc_type_bindings_from_type_bound(trait_ref.clone());
                    }
                    clause = Some(Clause(Predicate::new(
                        interner,
                        Binder::dummy(rustc_type_ir::PredicateKind::Clause(
                            rustc_type_ir::ClauseKind::Trait(TraitPredicate {
                                trait_ref,
                                polarity: rustc_type_ir::PredicatePolarity::Positive,
                            }),
                        )),
                    )));
                }
            }
            &TypeBound::Path(path, TraitBoundModifier::Maybe) => {
                let sized_trait = self
                    .db
                    .lang_item(self.resolver.krate(), LangItem::Sized)
                    .and_then(|lang_item| lang_item.as_trait());
                // Don't lower associated type bindings as the only possible relaxed trait bound
                // `?Sized` has no of them.
                // If we got another trait here ignore the bound completely.
                let trait_id =
                    self.lower_trait_ref_from_path(path, self_ty.clone()).map(|(trait_ref, _)| {
                        match trait_ref.def_id {
                            SolverDefId::TraitId(id) => id,
                            _ => unreachable!(),
                        }
                    });
                if trait_id == sized_trait {
                    self.unsized_types.insert(self_ty);
                }
            }
            TypeBound::Lifetime(l) => {
                let lifetime = self.lower_lifetime(l);
                clause = Some(Clause(Predicate::new(
                    self.interner,
                    Binder::dummy(rustc_type_ir::PredicateKind::Clause(
                        rustc_type_ir::ClauseKind::TypeOutlives(OutlivesPredicate(
                            self_ty, lifetime,
                        )),
                    )),
                )));
            }
            TypeBound::Use(_) | TypeBound::Error => {}
        }
        clause.into_iter().chain(assoc_bounds.into_iter().flatten())
    }

    fn lower_dyn_trait(&mut self, bounds: &[TypeBound]) -> Ty<'db> {
        let interner = self.interner;
        // FIXME: we should never create non-existential predicates in the first place
        // For now, use an error type so we don't run into dummy binder issues
        let self_ty = Ty::new_error(interner, ErrorGuaranteed);
        // INVARIANT: The principal trait bound, if present, must come first. Others may be in any
        // order but should be in the same order for the same set but possibly different order of
        // bounds in the input.
        // INVARIANT: If this function returns `DynTy`, there should be at least one trait bound.
        // These invariants are utilized by `TyExt::dyn_trait()` and chalk.
        let mut lifetime = None;
        let bounds = self.with_shifted_in(DebruijnIndex::from_u32(1), |ctx| {
            let mut lowered_bounds: Vec<
                rustc_type_ir::Binder<DbInterner<'db>, ExistentialPredicate<DbInterner<'db>>>,
            > = Vec::new();
            for b in bounds {
                let db = ctx.db;
                ctx.lower_type_bound(b, self_ty.clone(), false).for_each(|b| {
                    if let Some(bound) = b
                        .kind()
                        .map_bound(|c| match c {
                            rustc_type_ir::ClauseKind::Trait(t) => {
                                let id = t.def_id();
                                let id = match id {
                                    SolverDefId::TraitId(id) => id,
                                    _ => unreachable!(),
                                };
                                let is_auto =
                                    db.trait_signature(id).flags.contains(TraitFlags::AUTO);
                                if is_auto {
                                    Some(ExistentialPredicate::AutoTrait(t.def_id()))
                                } else {
                                    Some(ExistentialPredicate::Trait(
                                        ExistentialTraitRef::new_from_args(
                                            interner,
                                            t.def_id(),
                                            GenericArgs::new_from_iter(
                                                interner,
                                                t.trait_ref.args.iter().skip(1),
                                            ),
                                        ),
                                    ))
                                }
                            }
                            rustc_type_ir::ClauseKind::Projection(p) => {
                                Some(ExistentialPredicate::Projection(
                                    ExistentialProjection::new_from_args(
                                        interner,
                                        p.def_id(),
                                        GenericArgs::new_from_iter(
                                            interner,
                                            p.projection_term.args.iter().skip(1),
                                        ),
                                        p.term,
                                    ),
                                ))
                            }
                            rustc_type_ir::ClauseKind::TypeOutlives(outlives_predicate) => {
                                lifetime = Some(outlives_predicate.1);
                                None
                            }
                            rustc_type_ir::ClauseKind::RegionOutlives(_)
                            | rustc_type_ir::ClauseKind::ConstArgHasType(_, _)
                            | rustc_type_ir::ClauseKind::WellFormed(_)
                            | rustc_type_ir::ClauseKind::ConstEvaluatable(_)
                            | rustc_type_ir::ClauseKind::HostEffect(_) => unreachable!(),
                        })
                        .transpose()
                    {
                        lowered_bounds.push(bound);
                    }
                })
            }

            let mut multiple_regular_traits = false;
            let mut multiple_same_projection = false;
            lowered_bounds.sort_unstable_by(|lhs, rhs| {
                use std::cmp::Ordering;
                match (lhs.clone().skip_binder(), rhs.clone().skip_binder()) {
                    (ExistentialPredicate::Trait(_), ExistentialPredicate::Trait(_)) => {
                        multiple_regular_traits = true;
                        // Order doesn't matter - we error
                        Ordering::Equal
                    }
                    (
                        ExistentialPredicate::AutoTrait(lhs_id),
                        ExistentialPredicate::AutoTrait(rhs_id),
                    ) => {
                        let lhs_id = match lhs_id {
                            SolverDefId::TraitId(id) => id,
                            _ => unreachable!(),
                        };
                        let rhs_id = match rhs_id {
                            SolverDefId::TraitId(id) => id,
                            _ => unreachable!(),
                        };
                        lhs_id.cmp(&rhs_id)
                    }
                    (ExistentialPredicate::Trait(_), _) => Ordering::Less,
                    (_, ExistentialPredicate::Trait(_)) => Ordering::Greater,
                    (ExistentialPredicate::AutoTrait(_), _) => Ordering::Less,
                    (_, ExistentialPredicate::AutoTrait(_)) => Ordering::Greater,
                    (
                        ExistentialPredicate::Projection(lhs),
                        ExistentialPredicate::Projection(rhs),
                    ) => {
                        let lhs_id = match lhs.def_id {
                            SolverDefId::TypeAliasId(id) => id,
                            _ => unreachable!(),
                        };
                        let rhs_id = match rhs.def_id {
                            SolverDefId::TypeAliasId(id) => id,
                            _ => unreachable!(),
                        };
                        // We only compare the `associated_ty_id`s. We shouldn't have
                        // multiple bounds for an associated type in the correct Rust code,
                        // and if we do, we error out.
                        if lhs_id == rhs_id {
                            multiple_same_projection = true;
                        }
                        lhs_id.as_id().as_u32().cmp(&rhs_id.as_id().as_u32())
                    }
                }
            });

            if multiple_regular_traits || multiple_same_projection {
                return None;
            }

            if !lowered_bounds.first().map_or(false, |b| {
                matches!(
                    b.as_ref().skip_binder(),
                    ExistentialPredicate::Trait(_) | ExistentialPredicate::AutoTrait(_)
                )
            }) {
                return None;
            }

            // As multiple occurrences of the same auto traits *are* permitted, we deduplicate the
            // bounds. We shouldn't have repeated elements besides auto traits at this point.
            lowered_bounds.dedup();

            Some(BoundExistentialPredicates::new_from_iter(interner, lowered_bounds))
        });

        if let Some(bounds) = bounds {
            let region = match lifetime {
                Some(it) => match it.clone().kind() {
                    rustc_type_ir::RegionKind::ReBound(db, var) => Region::new_bound(
                        self.interner,
                        db.shifted_out_to_binder(DebruijnIndex::from_u32(2)),
                        var,
                    ),
                    _ => it,
                },
                None => Region::new_static(self.interner),
            };
            Ty::new_dynamic(self.interner, bounds, region, rustc_type_ir::DynKind::Dyn)
        } else {
            // FIXME: report error
            // (additional non-auto traits, associated type rebound, or no resolved trait)
            Ty::new_error(self.interner, ErrorGuaranteed)
        }
    }

    fn lower_impl_trait(
        &mut self,
        def_id: SolverDefId,
        bounds: &[TypeBound],
        krate: Crate,
    ) -> ImplTrait<'db> {
        let interner = self.interner;
        cov_mark::hit!(lower_rpit);
        let args = GenericArgs::identity_for_item(interner, def_id);
        let self_ty = Ty::new_alias(
            self.interner,
            rustc_type_ir::AliasTyKind::Opaque,
            AliasTy::new_from_args(interner, def_id, args),
        );
        let predicates = self.with_shifted_in(DebruijnIndex::from_u32(1), |ctx| {
            let mut predicates = Vec::new();
            for b in bounds {
                predicates.extend(ctx.lower_type_bound(b, self_ty.clone(), false));
            }

            if !ctx.unsized_types.contains(&self_ty) {
                let sized_trait = ctx.db.lang_item(krate, LangItem::Sized);
                let sized_clause = sized_trait.map(|trait_id| {
                    let trait_ref = TraitRef::new_from_args(
                        interner,
                        trait_id.as_trait().unwrap().into(),
                        GenericArgs::new_from_iter(interner, [self_ty.clone().into()]),
                    );
                    Clause(Predicate::new(
                        interner,
                        Binder::dummy(rustc_type_ir::PredicateKind::Clause(
                            rustc_type_ir::ClauseKind::Trait(TraitPredicate {
                                trait_ref,
                                polarity: rustc_type_ir::PredicatePolarity::Positive,
                            }),
                        )),
                    ))
                });
                predicates.extend(sized_clause);
            }
            predicates.shrink_to_fit();
            predicates
        });
        ImplTrait { predicates }
    }

    fn lower_lifetime(&self, lifetime: &LifetimeRef) -> Region<'db> {
        match self.resolver.resolve_lifetime(lifetime) {
            Some(resolution) => match resolution {
                LifetimeNs::Static => Region::new_static(self.interner),
                LifetimeNs::LifetimeParam(id) => {
                    let idx = match self.generics().lifetime_idx(id) {
                        None => return Region::error(self.interner),
                        Some(idx) => idx,
                    };
                    Region::new_early_param(self.interner, EarlyParamRegion { index: idx as u32 })
                }
            },
            None => Region::error(self.interner),
        }
    }
}

pub(crate) fn named_associated_type_shorthand_candidates<'a>(
    db: &'a dyn HirDatabase,
    krate: Crate,
    // If the type parameter is defined in an impl and we're in a method, there
    // might be additional where clauses to consider
    def: GenericDefId,
    res: TypeNs,
    assoc_name: Option<Name>,
    // Do NOT let `cb` touch `TraitRef` outside of `TyLoweringContext`. Its substitution contains
    // free `BoundVar`s that need to be shifted and only `TyLoweringContext` knows how to do that
    // properly (see `TyLoweringContext::select_associated_type()`).
    mut cb: impl FnMut(&Name, &TraitRef<'a>, TypeAliasId) -> Option<Ty<'a>>,
) -> Option<Ty<'a>> {
    let interner = DbInterner::new_with(db, Some(krate), None);
    let mut check_trait_ref = |t: &TraitRef<'a>| {
        let trait_id = match t.def_id {
            SolverDefId::TraitId(id) => id,
            _ => unreachable!(),
        };
        let data = db.trait_items(trait_id);

        for (name, assoc_id) in &data.items {
            if let AssocItemId::TypeAliasId(alias) = assoc_id {
                if let Some(result) = cb(name, t, *alias) {
                    return Some(result);
                }
            }
        }
        None
    };
    let mut search = |t: TraitRef<'a>| {
        // Before elaborating supertraits, check the current one first.
        // This is because `elaborate::supertraits` gets the super predicates
        // *before* returning here. So, if the associated type is on the
        // current trait, we will end up in a cycle.
        // FIXME: this is not quite correct for a couple reasons:
        // 1) This only avoids cycle at the first trait ref - so, if there would
        //    be a cycle in the super trait refs, this doesn't avoid it
        // 2) I think this is still an incomplete solution when there are *other*
        //    associated types and predicates around and we could get into a
        //    double-cycle - I think we *always* need to avoid calling the
        //    `generic_predicates_for_param` and instead follow rustc's approach
        //    like filtering for traits that *could* define the associated type
        //    first.
        if let Some(ty) = check_trait_ref(&t) {
            return Some(ty);
        }
        rustc_type_ir::elaborate::supertraits(interner, Binder::dummy(t))
            .find_map(|t| check_trait_ref(t.as_ref().skip_binder()))
    };

    match res {
        TypeNs::SelfType(impl_id) => {
            // we're _in_ the impl -- the binders get added back later. Correct,
            // but it would be nice to make this more explicit
            // FIXME: use db query
            let trait_ref = impl_trait_query(db, impl_id)?;
            search(trait_ref.skip_binder())
        }
        TypeNs::GenericParam(param_id) => {
            // Handle `Self::Type` referring to own associated type in trait definitions
            // This *must* be done first to avoid cycles with
            // `generic_predicates_for_param`, but not sure that it's sufficient,
            // see FIXME in `search`.
            if let GenericDefId::TraitId(trait_id) = param_id.parent() {
                let trait_generics = generics(db, trait_id.into());
                let trait_self = trait_generics[param_id.local_id()].is_trait_self();
                if trait_generics[param_id.local_id()].is_trait_self() {
                    let args = GenericArgs::identity_for_item(interner, trait_id.into());
                    let trait_ref = TraitRef::new_from_args(interner, trait_id.into(), args);
                    return search(trait_ref);
                }
            }

            let predicates =
                generic_predicates_for_param_query(db, def, param_id.into(), assoc_name);
            let res = predicates.iter().find_map(|pred| match pred.clone().kind().skip_binder() {
                rustc_type_ir::ClauseKind::Trait(trait_predicate) => {
                    let trait_ref = trait_predicate.trait_ref;
                    assert!(
                        !trait_ref.has_escaping_bound_vars(),
                        "FIXME unexpected higher-ranked trait bound"
                    );
                    search(trait_ref)
                }
                _ => None,
            });
            if res.is_some() {
                return res;
            }
            None
        }
        _ => None,
    }
}

pub(crate) fn lower_mutability(m: hir_def::type_ref::Mutability) -> Mutability {
    match m {
        hir_def::type_ref::Mutability::Shared => Mutability::Not,
        hir_def::type_ref::Mutability::Mut => Mutability::Mut,
    }
}

fn unknown_const(_ty: Ty<'_>) -> Const<'_> {
    Const::new(DbInterner::new(), ConstKind::Error(ErrorGuaranteed))
}

pub(crate) fn impl_trait_query<'db>(
    db: &'db dyn HirDatabase,
    impl_id: ImplId,
) -> Option<EarlyBinder<'db, TraitRef<'db>>> {
    impl_trait_with_diagnostics_query(db, impl_id).map(|it| it.0)
}

pub(crate) fn impl_trait_with_diagnostics_query<'db>(
    db: &'db dyn HirDatabase,
    impl_id: ImplId,
) -> Option<(EarlyBinder<'db, TraitRef<'db>>, Diagnostics)> {
    let impl_data = db.impl_signature(impl_id);
    let resolver = impl_id.resolver(db);
    let mut ctx = TyLoweringContext::new(db, &resolver, &impl_data.store, impl_id.into());
    let self_ty = impl_self_ty_query(db, impl_id).skip_binder();
    let target_trait = impl_data.target_trait.as_ref()?;
    let trait_ref = EarlyBinder::bind(ctx.lower_trait_ref(target_trait, self_ty)?);
    Some((trait_ref, create_diagnostics(ctx.diagnostics)))
}

pub(crate) fn return_type_impl_traits<'db>(
    db: &'db dyn HirDatabase,
    def: hir_def::FunctionId,
) -> Option<Arc<EarlyBinder<'db, ImplTraits<'db>>>> {
    // FIXME unify with fn_sig_for_fn instead of doing lowering twice, maybe
    let data = db.function_signature(def);
    let resolver = def.resolver(db);
    let mut ctx_ret = TyLoweringContext::new(db, &resolver, &data.store, def.into())
        .with_impl_trait_mode(ImplTraitLoweringMode::Opaque);
    if let Some(ret_type) = data.ret_type {
        let _ret = ctx_ret.lower_ty(ret_type);
    }
    let return_type_impl_traits =
        ImplTraits { impl_traits: ctx_ret.impl_trait_mode.opaque_type_data };
    if return_type_impl_traits.impl_traits.is_empty() {
        None
    } else {
        Some(Arc::new(EarlyBinder::bind(return_type_impl_traits)))
    }
}

pub(crate) fn type_alias_impl_traits<'db>(
    db: &'db dyn HirDatabase,
    def: hir_def::TypeAliasId,
) -> Option<Arc<EarlyBinder<'db, ImplTraits<'db>>>> {
    let data = db.type_alias_signature(def);
    let resolver = def.resolver(db);
    let mut ctx = TyLoweringContext::new(db, &resolver, &data.store, def.into())
        .with_impl_trait_mode(ImplTraitLoweringMode::Opaque);
    if let Some(type_ref) = data.ty {
        let _ty = ctx.lower_ty(type_ref);
    }
    let type_alias_impl_traits = ImplTraits { impl_traits: ctx.impl_trait_mode.opaque_type_data };
    if type_alias_impl_traits.impl_traits.is_empty() {
        None
    } else {
        Some(Arc::new(EarlyBinder::bind(type_alias_impl_traits)))
    }
}

/// Build the declared type of an item. This depends on the namespace; e.g. for
/// `struct Foo(usize)`, we have two types: The type of the struct itself, and
/// the constructor function `(usize) -> Foo` which lives in the values
/// namespace.
pub(crate) fn ty_query<'db>(db: &'db dyn HirDatabase, def: TyDefId) -> EarlyBinder<'db, Ty<'db>> {
    let interner = DbInterner::new_with(db, None, None);
    match def {
        TyDefId::BuiltinType(it) => EarlyBinder::bind(builtin(interner, it)),
        TyDefId::AdtId(it) => EarlyBinder::bind(Ty::new_adt(
            interner,
            AdtDef::new(it, interner),
            GenericArgs::identity_for_item(interner, it.into()),
        )),
        TyDefId::TypeAliasId(it) => type_for_type_alias_with_diagnostics_query(db, it).0,
    }
}

fn type_for_type_alias_with_diagnostics_query<'db>(
    db: &'db dyn HirDatabase,
    t: TypeAliasId,
) -> (EarlyBinder<'db, Ty<'db>>, Diagnostics) {
    let type_alias_data = db.type_alias_signature(t);
    let mut diags = None;
    let inner = if type_alias_data.flags.contains(TypeAliasFlags::IS_EXTERN) {
        EarlyBinder::bind(Ty::new_foreign(DbInterner::new(), t.into()))
    } else {
        let resolver = t.resolver(db);
        let mut ctx = TyLoweringContext::new(db, &resolver, &type_alias_data.store, t.into())
            .with_impl_trait_mode(ImplTraitLoweringMode::Opaque);
        let res = EarlyBinder::bind(
            type_alias_data
                .ty
                .map(|type_ref| ctx.lower_ty(type_ref))
                .unwrap_or_else(|| Ty::new_error(DbInterner::new(), ErrorGuaranteed)),
        );
        diags = create_diagnostics(ctx.diagnostics);
        res
    };
    (inner, diags)
}

pub(crate) fn impl_self_ty_query<'db>(
    db: &'db dyn HirDatabase,
    impl_id: ImplId,
) -> EarlyBinder<'db, Ty<'db>> {
    impl_self_ty_with_diagnostics_query(db, impl_id).0
}

pub(crate) fn impl_self_ty_with_diagnostics_query<'db>(
    db: &'db dyn HirDatabase,
    impl_id: ImplId,
) -> (EarlyBinder<'db, Ty<'db>>, Diagnostics) {
    // HACK HACK HACK delete pls
    thread_local! {
        static REENTRANT_MAP: std::cell::RefCell<HashSet<ImplId>> = std::cell::RefCell::new(HashSet::new());
    }
    let new = REENTRANT_MAP.with_borrow_mut(|m| m.insert(impl_id));
    if !new {
        REENTRANT_MAP.with_borrow_mut(|m| {
            m.remove(&impl_id);
        });
        return (EarlyBinder::bind(Ty::new_error(DbInterner::new(), ErrorGuaranteed)), None);
    }

    let impl_data = db.impl_signature(impl_id);
    let resolver = impl_id.resolver(db);
    let mut ctx = TyLoweringContext::new(db, &resolver, &impl_data.store, impl_id.into());
    let ty = ctx.lower_ty(impl_data.self_ty);
    assert!(!ty.has_escaping_bound_vars());
    REENTRANT_MAP.with_borrow_mut(|m| {
        m.remove(&impl_id);
    });
    (EarlyBinder::bind(ty), create_diagnostics(ctx.diagnostics))
}

pub(crate) fn const_param_ty_query<'db>(db: &'db dyn HirDatabase, def: ConstParamId) -> Ty<'db> {
    const_param_ty_with_diagnostics_query(db, def).0
}

// returns None if def is a type arg
pub(crate) fn const_param_ty_with_diagnostics_query<'db>(
    db: &'db dyn HirDatabase,
    def: ConstParamId,
) -> (Ty<'db>, Diagnostics) {
    let (parent_data, store) = db.generic_params_and_store(def.parent());
    let data = &parent_data[def.local_id()];
    let resolver = def.parent().resolver(db);
    let mut ctx = TyLoweringContext::new(db, &resolver, &store, def.parent().into());
    let ty = match data {
        TypeOrConstParamData::TypeParamData(_) => {
            never!();
            Ty::new_error(DbInterner::new(), ErrorGuaranteed)
        }
        TypeOrConstParamData::ConstParamData(d) => ctx.lower_ty(d.ty),
    };
    (ty, create_diagnostics(ctx.diagnostics))
}

pub(crate) fn field_types_query<'db>(
    db: &'db dyn HirDatabase,
    variant_id: VariantId,
) -> Arc<ArenaMap<LocalFieldId, EarlyBinder<'db, Ty<'db>>>> {
    field_types_with_diagnostics_query(db, variant_id).0
}

/// Build the type of all specific fields of a struct or enum variant.
pub(crate) fn field_types_with_diagnostics_query<'db>(
    db: &'db dyn HirDatabase,
    variant_id: VariantId,
) -> (Arc<ArenaMap<LocalFieldId, EarlyBinder<'db, Ty<'db>>>>, Diagnostics) {
    let var_data = variant_id.variant_data(db);
    let (resolver, def): (_, GenericDefId) = match variant_id {
        VariantId::StructId(it) => (it.resolver(db), it.into()),
        VariantId::UnionId(it) => (it.resolver(db), it.into()),
        VariantId::EnumVariantId(it) => (it.resolver(db), it.lookup(db).parent.into()),
    };
    let mut res = ArenaMap::default();
    let mut ctx = TyLoweringContext::new(db, &resolver, &var_data.store, def.into());
    for (field_id, field_data) in var_data.fields().iter() {
        res.insert(field_id, EarlyBinder::bind(ctx.lower_ty(field_data.type_ref)));
    }
    (Arc::new(res), create_diagnostics(ctx.diagnostics))
}

/// This query exists only to be used when resolving short-hand associated types
/// like `T::Item`.
///
/// See the analogous query in rustc and its comment:
/// <https://github.com/rust-lang/rust/blob/9150f844e2624eb013ec78ca08c1d416e6644026/src/librustc_typeck/astconv.rs#L46>
/// This is a query mostly to handle cycles somewhat gracefully; e.g. the
/// following bounds are disallowed: `T: Foo<U::Item>, U: Foo<T::Item>`, but
/// these are fine: `T: Foo<U::Item>, U: Foo<()>`.
#[tracing::instrument(skip(db), ret)]
pub(crate) fn generic_predicates_for_param_query<'db>(
    db: &'db dyn HirDatabase,
    def: GenericDefId,
    param_id: TypeOrConstParamId,
    assoc_name: Option<Name>,
) -> GenericPredicates<'db> {
    let generics = generics(db, def);
    let interner = DbInterner::new_with(db, None, None);
    let resolver = def.resolver(db);
    let mut ctx = TyLoweringContext::new(db, &resolver, generics.store(), def);

    // we have to filter out all other predicates *first*, before attempting to lower them
    let predicate = |pred: &_, generics: &Generics, ctx: &mut TyLoweringContext<'_, '_>| match pred
    {
        WherePredicate::ForLifetime { target, bound, .. }
        | WherePredicate::TypeBound { target, bound, .. } => {
            let invalid_target = match target {
                WherePredicateTypeTarget::TypeRef(type_ref) => {
                    let ty = ctx.lower_ty_only_param(*type_ref);
                    tracing::debug!(?ty);
                    ty != Some(param_id)
                }
                &WherePredicateTypeTarget::TypeOrConstParam(local_id) => {
                    let target_id = TypeOrConstParamId { parent: generics.def(), local_id };
                    target_id != param_id
                }
            };
            if invalid_target {
                // If this is filtered out without lowering, `?Sized` is not gathered into `ctx.unsized_types`
                if let TypeBound::Path(_, TraitBoundModifier::Maybe) = bound {
                    ctx.lower_where_predicate(pred, generics, generics.def(), true).for_each(drop);
                }
                return false;
            }

            match bound {
                &TypeBound::ForLifetime(_, path) | &TypeBound::Path(path, _) => {
                    // Only lower the bound if the trait could possibly define the associated
                    // type we're looking for.
                    let path = &ctx.store[path];

                    let Some(assoc_name) = &assoc_name else { return true };
                    let Some(TypeNs::TraitId(tr)) =
                        resolver.resolve_path_in_type_ns_fully(db, path)
                    else {
                        return false;
                    };

                    rustc_type_ir::elaborate::supertrait_def_ids(interner, tr.into()).any(|tr| {
                        let tr = match tr {
                            SolverDefId::TraitId(id) => id,
                            _ => unreachable!(),
                        };
                        db.trait_items(tr).items.iter().any(|(name, item)| {
                            matches!(item, AssocItemId::TypeAliasId(_)) && name == assoc_name
                        })
                    })
                }
                TypeBound::Use(_) | TypeBound::Lifetime(_) | TypeBound::Error => false,
            }
        }
        WherePredicate::Lifetime { .. } => false,
    };
    let mut predicates = Vec::new();
    for maybe_parent_generics in
        std::iter::successors(Some(&generics), |generics| generics.parent_generics())
    {
        ctx.store = maybe_parent_generics.store();
        for pred in maybe_parent_generics.where_predicates() {
            if predicate(pred, maybe_parent_generics, &mut ctx) {
                predicates.extend(ctx.lower_where_predicate(
                    pred,
                    &generics,
                    maybe_parent_generics.def(),
                    true,
                ));
            }
        }
    }

    let args = GenericArgs::identity_for_item(interner, def.into());
    if !args.clone().is_empty() {
        let explicitly_unsized_tys = ctx.unsized_types;
        if let Some(implicitly_sized_predicates) =
            implicitly_sized_clauses(db, param_id.parent, &explicitly_unsized_tys, &args, &resolver)
        {
            predicates.extend(implicitly_sized_predicates);
        };
    }
    GenericPredicates(predicates.is_empty().not().then(|| predicates.into()))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericPredicates<'db>(Option<Arc<[Clause<'db>]>>);

impl<'db> ops::Deref for GenericPredicates<'db> {
    type Target = [Clause<'db>];

    fn deref(&self) -> &Self::Target {
        self.0.as_deref().unwrap_or(&[])
    }
}

/// Resolve the where clause(s) of an item with generics.
pub(crate) fn generic_predicates_query<'db>(
    db: &'db dyn HirDatabase,
    def: GenericDefId,
) -> GenericPredicates<'db> {
    generic_predicates_filtered_by(db, def, |_| true).0
}

pub(crate) fn generic_predicates_without_parent_query<'db>(
    db: &'db dyn HirDatabase,
    def: GenericDefId,
) -> GenericPredicates<'db> {
    generic_predicates_filtered_by(db, def, |d| d == def).0
}

/// Resolve the where clause(s) of an item with generics,
/// except the ones inherited from the parent
pub(crate) fn generic_predicates_without_parent_with_diagnostics_query<'db>(
    db: &'db dyn HirDatabase,
    def: GenericDefId,
) -> (GenericPredicates<'db>, Diagnostics) {
    generic_predicates_filtered_by(db, def, |d| d == def)
}

/// Resolve the where clause(s) of an item with generics,
/// with a given filter
#[tracing::instrument(skip(db, filter), ret)]
pub(crate) fn generic_predicates_filtered_by<'db, F>(
    db: &'db dyn HirDatabase,
    def: GenericDefId,
    filter: F,
) -> (GenericPredicates<'db>, Diagnostics)
where
    F: Fn(GenericDefId) -> bool,
{
    let generics = generics(db, def);
    let resolver = def.resolver(db);
    let interner = DbInterner::new_with(db, Some(resolver.krate()), None);
    let mut ctx = TyLoweringContext::new(db, &resolver, generics.store(), def.into());

    let mut predicates = Vec::new();
    for maybe_parent_generics in
        std::iter::successors(Some(&generics), |generics| generics.parent_generics())
    {
        ctx.store = maybe_parent_generics.store();
        for pred in maybe_parent_generics.where_predicates() {
            if filter(maybe_parent_generics.def()) {
                // We deliberately use `generics` and not `maybe_parent_generics` here. This is not a mistake!
                // If we use the parent generics
                predicates.extend(ctx.lower_where_predicate(
                    pred,
                    &generics,
                    maybe_parent_generics.def(),
                    false,
                ));
            }
        }
    }

    let explicitly_unsized_tys = ctx.unsized_types;

    let sized_trait =
        db.lang_item(resolver.krate(), LangItem::Sized).and_then(|lang_item| lang_item.as_trait());

    if let Some(sized_trait) = sized_trait {
        for (params, def) in resolver.all_generic_params() {
            if !filter(*def) {
                continue;
            }
            let len_lt = params.len_lifetimes() as u32;
            for (idx, data) in params.iter_type_or_consts() {
                if data.is_trait_self() {
                    continue;
                }
                if let Some(param) = data.type_param() {
                    let idx = idx.into_raw().into_u32() + len_lt;
                    let name = param
                        .name
                        .as_ref()
                        .map(|n| n.symbol().clone())
                        .unwrap_or_else(|| Name::missing().symbol().clone());
                    let param_ty = Ty::new_param(DbInterner::new(), idx, name).into();
                    if explicitly_unsized_tys.contains(&param_ty) {
                        continue;
                    }
                    let trait_ref = TraitRef::new_from_args(
                        interner,
                        sized_trait.into(),
                        GenericArgs::new_from_iter(interner, [param_ty.clone().into()]),
                    );
                    let clause = Clause(Predicate::new(
                        interner,
                        Binder::dummy(rustc_type_ir::PredicateKind::Clause(
                            rustc_type_ir::ClauseKind::Trait(TraitPredicate {
                                trait_ref,
                                polarity: rustc_type_ir::PredicatePolarity::Positive,
                            }),
                        )),
                    ));
                    predicates.push(clause);
                }
            }
        }
    }

    (
        GenericPredicates(predicates.is_empty().not().then(|| predicates.into())),
        create_diagnostics(ctx.diagnostics),
    )
}

/// Generate implicit `: Sized` predicates for all generics that has no `?Sized` bound.
/// Exception is Self of a trait def.
fn implicitly_sized_clauses<'a, 'subst, 'db>(
    db: &'db dyn HirDatabase,
    def: GenericDefId,
    explicitly_unsized_tys: &'a FxHashSet<Ty<'db>>,
    args: &'subst GenericArgs<'db>,
    resolver: &Resolver,
) -> Option<impl Iterator<Item = Clause<'db>> + Captures<'a> + Captures<'subst>> {
    let interner = DbInterner::new_with(db, Some(resolver.krate()), None);
    let sized_trait = db
        .lang_item(resolver.krate(), LangItem::Sized)
        .and_then(|lang_item| lang_item.as_trait())?;

    let trait_self_idx = trait_self_param_idx(db, def);

    Some(
        args.iter()
            .enumerate()
            .filter_map(
                move |(idx, generic_arg)| {
                    if Some(idx) == trait_self_idx { None } else { Some(generic_arg) }
                },
            )
            .filter_map(|generic_arg| generic_arg.as_type())
            .filter(move |self_ty| !explicitly_unsized_tys.contains(self_ty))
            .map(move |self_ty| {
                let trait_ref = TraitRef::new_from_args(
                    interner,
                    sized_trait.into(),
                    GenericArgs::new_from_iter(interner, [self_ty.into()]),
                );
                Clause(Predicate::new(
                    interner,
                    Binder::dummy(rustc_type_ir::PredicateKind::Clause(
                        rustc_type_ir::ClauseKind::Trait(TraitPredicate {
                            trait_ref,
                            polarity: rustc_type_ir::PredicatePolarity::Positive,
                        }),
                    )),
                ))
            }),
    )
}

pub(crate) fn make_binders<'db, T: rustc_type_ir::TypeVisitable<DbInterner<'db>>>(
    interner: DbInterner<'db>,
    generics: &Generics,
    value: T,
) -> Binder<'db, T> {
    Binder::bind_with_vars(
        value,
        BoundVarKinds::new_from_iter(
            interner,
            generics.iter_id().map(|x| match x {
                hir_def::GenericParamId::ConstParamId(_) => BoundVarKind::Const,
                hir_def::GenericParamId::TypeParamId(_) => BoundVarKind::Ty(BoundTyKind::Anon),
                hir_def::GenericParamId::LifetimeParamId(_) => {
                    BoundVarKind::Region(BoundRegionKind::Anon)
                }
            }),
        ),
    )
}

/// Checks if the provided generic arg matches its expected kind, then lower them via
/// provided closures. Use unknown if there was kind mismatch.
///
pub(crate) fn lower_generic_arg<'a, 'db, T>(
    db: &'db dyn HirDatabase,
    kind_id: GenericParamId,
    arg: &'a GenericArg,
    this: &mut T,
    store: &ExpressionStore,
    for_type: impl FnOnce(&mut T, TypeRefId) -> Ty<'db> + 'a,
    for_const: impl FnOnce(&mut T, &ConstRef, Ty<'db>) -> Const<'db> + 'a,
    for_const_ty_path_fallback: impl FnOnce(&mut T, &Path, Ty<'db>) -> Const<'db> + 'a,
    for_lifetime: impl FnOnce(&mut T, &LifetimeRef) -> Region<'db> + 'a,
) -> crate::next_solver::GenericArg<'db> {
    let interner = DbInterner::new_with(db, None, None);
    let kind = match kind_id {
        GenericParamId::TypeParamId(_) => ParamKind::Type,
        GenericParamId::ConstParamId(id) => {
            let ty = db.const_param_ty(id);
            ParamKind::Const(ty)
        }
        GenericParamId::LifetimeParamId(_) => ParamKind::Lifetime,
    };
    match (arg, kind) {
        (GenericArg::Type(type_ref), ParamKind::Type) => for_type(this, *type_ref).into(),
        (GenericArg::Const(c), ParamKind::Const(c_ty)) => {
            for_const(this, c, c_ty.to_nextsolver(interner)).into()
        }
        (GenericArg::Lifetime(lifetime_ref), ParamKind::Lifetime) => {
            for_lifetime(this, lifetime_ref).into()
        }
        (GenericArg::Const(_), ParamKind::Type) => {
            Ty::new_error(DbInterner::new(), ErrorGuaranteed).into()
        }
        (GenericArg::Lifetime(_), ParamKind::Type) => {
            Ty::new_error(DbInterner::new(), ErrorGuaranteed).into()
        }
        (GenericArg::Type(t), ParamKind::Const(c_ty)) => match &store[*t] {
            TypeRef::Path(p) => {
                for_const_ty_path_fallback(this, p, c_ty.to_nextsolver(interner)).into()
            }
            _ => unknown_const_as_generic(c_ty.to_nextsolver(interner)),
        },
        (GenericArg::Lifetime(_), ParamKind::Const(c_ty)) => {
            unknown_const(c_ty.to_nextsolver(interner)).into()
        }
        (GenericArg::Type(_), ParamKind::Lifetime) => Region::error(interner).into(),
        (GenericArg::Const(_), ParamKind::Lifetime) => Region::error(interner).into(),
    }
}

/// Build the signature of a callable item (function, struct or enum variant).
pub(crate) fn callable_item_sig<'db>(
    db: &'db dyn HirDatabase,
    def: CallableDefId,
) -> EarlyBinder<'db, PolyFnSig<'db>> {
    match def {
        CallableDefId::FunctionId(f) => fn_sig_for_fn(db, f),
        CallableDefId::StructId(s) => fn_sig_for_struct_constructor(db, s),
        CallableDefId::EnumVariantId(e) => fn_sig_for_enum_variant_constructor(db, e),
    }
}

fn fn_sig_for_fn<'db>(
    db: &'db dyn HirDatabase,
    def: FunctionId,
) -> EarlyBinder<'db, PolyFnSig<'db>> {
    let data = db.function_signature(def);
    let resolver = def.resolver(db);
    let interner = DbInterner::new_with(db, Some(resolver.krate()), None);
    let mut ctx_params = TyLoweringContext::new(db, &resolver, &data.store, def.into());
    let params = data.params.iter().map(|&tr| ctx_params.lower_ty(tr));

    let ret = match data.ret_type {
        Some(ret_type) => {
            let mut ctx_ret = TyLoweringContext::new(db, &resolver, &data.store, def.into())
                .with_impl_trait_mode(ImplTraitLoweringMode::Opaque);
            ctx_ret.lower_ty(ret_type)
        }
        None => Ty::new_tup(interner, &[]),
    };

    let inputs_and_output = Tys::new_from_iter(DbInterner::new(), params.chain(Some(ret)));
    // If/when we track late bound vars, we need to switch this to not be `dummy`
    EarlyBinder::bind(rustc_type_ir::Binder::dummy(FnSig {
        abi: data.abi.as_ref().map_or(FnAbi::Rust, FnAbi::from_symbol),
        c_variadic: data.is_varargs(),
        safety: if data.is_unsafe() { Safety::Unsafe } else { Safety::Safe },
        inputs_and_output,
    }))
}

fn type_for_adt<'db>(db: &'db dyn HirDatabase, adt: AdtId) -> EarlyBinder<'db, Ty<'db>> {
    let interner = DbInterner::new_with(db, None, None);
    let args = GenericArgs::identity_for_item(interner, adt.into());
    let ty = Ty::new_adt(DbInterner::new(), AdtDef::new(adt.into(), interner), args);
    EarlyBinder::bind(ty)
}

fn fn_sig_for_struct_constructor<'db>(
    db: &'db dyn HirDatabase,
    def: StructId,
) -> EarlyBinder<'db, PolyFnSig<'db>> {
    let struct_data = db.variant_fields(def.into());
    let fields = struct_data.fields();
    let resolver = def.resolver(db);
    let mut ctx =
        TyLoweringContext::new(db, &resolver, &struct_data.store, AdtId::from(def).into());
    let params = fields.iter().map(|(_, field)| ctx.lower_ty(field.type_ref));
    let ret = type_for_adt(db, def.into()).skip_binder();

    let inputs_and_output = Tys::new_from_iter(DbInterner::new(), params.chain(Some(ret)));
    EarlyBinder::bind(Binder::dummy(FnSig {
        abi: FnAbi::RustCall,
        c_variadic: false,
        safety: Safety::Safe,
        inputs_and_output,
    }))
}

fn fn_sig_for_enum_variant_constructor<'db>(
    db: &'db dyn HirDatabase,
    def: EnumVariantId,
) -> EarlyBinder<'db, PolyFnSig<'db>> {
    let var_data = db.variant_fields(def.into());
    let fields = var_data.fields();
    let resolver = def.resolver(db);
    let parent = def.lookup(db).parent;
    let mut ctx = TyLoweringContext::new(db, &resolver, &var_data.store, parent.into());
    let params = fields.iter().map(|(_, field)| ctx.lower_ty(field.type_ref));
    let ret = type_for_adt(db, def.lookup(db).parent.into()).skip_binder();

    let inputs_and_output = Tys::new_from_iter(DbInterner::new(), params.chain(Some(ret)));
    EarlyBinder::bind(Binder::dummy(FnSig {
        abi: FnAbi::RustCall,
        c_variadic: false,
        safety: Safety::Safe,
        inputs_and_output,
    }))
}

pub fn associated_type_by_name_including_super_traits<'db>(
    db: &'db dyn HirDatabase,
    trait_ref: TraitRef<'db>,
    name: &Name,
) -> Option<(TraitRef<'db>, TypeAliasId)> {
    let interner = DbInterner::new_with(db, None, None);
    rustc_type_ir::elaborate::supertraits(interner, Binder::dummy(trait_ref)).find_map(|t| {
        let trait_id = match t.as_ref().skip_binder().def_id {
            SolverDefId::TraitId(id) => id,
            _ => unreachable!(),
        };
        let assoc_type = db.trait_items(trait_id).associated_type_by_name(name)?;
        Some((t.skip_binder(), assoc_type))
    })
}
