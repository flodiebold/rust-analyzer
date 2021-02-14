//! Lowering from `TypeRef` (our AST representation of types) to `Type`, which
//! is a representation with resolved names.
//!
//! Things this does that I'm not sure about:
//!  - add default type parameters
//!  - select associated types for shorthand (T::Item)
//!  - lower argument impl trait to parameters
use std::{
    cell::{Cell, RefCell},
    iter,
    sync::Arc,
};

use hir_def::{
    builtin_type::BuiltinType,
    generics::{TypeParamProvenance, WherePredicate, WherePredicateTypeTarget},
    path::{GenericArg, Path, PathSegment, PathSegments},
    resolver::{HasResolver, Resolver, TypeNs},
    type_ref::{TypeBound, TypeRef},
    AssocItemId, ConstId, ConstParamId, EnumVariantId, FunctionId, GenericDefId, ImplId, StaticId,
    StructId, TraitId, TypeAliasId, TypeParamId,
};
use test_utils::mark;

use super::{
    substitute, ApplicationType, AssocTypeBinding, Bound, HirTypeWalk, OpaqueType, ProjectionType,
    TraitBound, Type, TypeArgs, TypeName, WhereClause,
};
use super::{FnSig, LoweredFn};
use crate::{
    db::HirDatabase,
    primitive::{FloatTy, IntTy},
    utils::generics,
    CallableDefId, OpaqueTyId, TyDefId, ValueTyDefId,
};
use hir_expand::name::Name;
use smallvec::SmallVec;

// FIXME make this private once lowering only goes through queries
pub(crate) struct Context<'a> {
    db: &'a dyn HirDatabase,
    resolver: &'a Resolver,
    impl_trait_mode: ImplTraitLoweringMode,
    impl_trait_counter: Cell<u16>,
    opaque_type_data: RefCell<Vec<SmallVec<[Bound; 1]>>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ImplTraitLoweringMode {
    /// `impl Trait` gets lowered into an opaque type. Used for return position
    /// impl Trait.
    Opaque,
    /// `impl Trait` gets lowered into a type variable. Used for argument
    /// position impl Trait.
    Param,
    /// `impl Trait` is disallowed and will be an error.
    Disallowed,
}

impl<'a> Context<'a> {
    pub fn new(db: &'a dyn HirDatabase, resolver: &'a Resolver) -> Self {
        Self {
            db,
            resolver,
            impl_trait_mode: ImplTraitLoweringMode::Disallowed,
            impl_trait_counter: Cell::new(0),
            opaque_type_data: RefCell::new(Vec::new()),
        }
    }

    pub fn with_impl_trait_mode(self, impl_trait_mode: ImplTraitLoweringMode) -> Self {
        Self { impl_trait_mode, ..self }
    }

    pub fn lower_type(&self, type_ref: &TypeRef) -> Type {
        self.lower_type_ext(type_ref).0
    }

    fn lower_type_ext(&self, type_ref: &TypeRef) -> (Type, Option<TypeNs>) {
        let mut res = None;
        let ty = match type_ref {
            TypeRef::Never => Type::simple(TypeName::Never),
            TypeRef::Tuple(inner) => {
                let arguments: TypeArgs = inner.iter().map(|tr| self.lower_type(tr)).collect();
                Type::apply(TypeName::Tuple { cardinality: arguments.len() as u16 }, arguments)
            }
            TypeRef::Path(path) => {
                let (ty, res_) = self.lower_path(path);
                res = res_;
                ty
            }
            TypeRef::RawPtr(inner, mutability) => {
                let inner_ty = self.lower_type(inner);
                Type::apply_one(TypeName::RawPtr(*mutability), inner_ty)
            }
            TypeRef::Array(inner) => {
                let inner_ty = self.lower_type(inner);
                Type::apply_one(TypeName::Array, inner_ty)
            }
            TypeRef::Slice(inner) => {
                let inner_ty = self.lower_type(inner);
                Type::apply_one(TypeName::Slice, inner_ty)
            }
            TypeRef::Reference(inner, _lifetime, mutability) => {
                let inner_ty = self.lower_type(inner);
                Type::apply_one(TypeName::Ref(*mutability), inner_ty)
            }
            TypeRef::Placeholder => Type::Infer,
            TypeRef::Fn(params, is_varargs) => {
                let sig: TypeArgs = params.iter().map(|tr| self.lower_type(tr)).collect();
                Type::apply(
                    TypeName::FnPtr { num_args: sig.len() as u16 - 1, is_varargs: *is_varargs },
                    sig,
                )
            }
            TypeRef::DynTrait(bounds) => {
                let predicates = bounds.iter().flat_map(|b| self.lower_bound(b)).collect();
                Type::Dyn(predicates)
            }
            TypeRef::ImplTrait(bounds) => {
                match self.impl_trait_mode {
                    ImplTraitLoweringMode::Opaque => {
                        mark::hit!(lower_rpit);
                        let idx = self.impl_trait_counter.get();
                        self.impl_trait_counter.set(idx + 1);

                        assert!(idx as usize == self.opaque_type_data.borrow().len());
                        // this dance is to make sure the data is in the right
                        // place even if we encounter more opaque types while
                        // lowering the bounds
                        self.opaque_type_data.borrow_mut().push(SmallVec::new());
                        // We don't want to lower the bounds inside the binders
                        // we're currently in, because they don't end up inside
                        // those binders. E.g. when we have `impl Trait<impl
                        // OtherTrait<T>>`, the `impl OtherTrait<T>` can't refer
                        // to the self parameter from `impl Trait`, and the
                        // bounds aren't actually stored nested within each
                        // other, but separately. So if the `T` refers to a type
                        // parameter of the outer function, it's just one binder
                        // away instead of two.
                        let predicates = bounds.iter().flat_map(|b| self.lower_bound(b)).collect();
                        self.opaque_type_data.borrow_mut()[idx as usize] = predicates;

                        let func = match self.resolver.generic_def() {
                            Some(GenericDefId::FunctionId(f)) => f,
                            _ => panic!("opaque impl trait lowering in non-function"),
                        };
                        let opaque_ty_id = OpaqueTyId::ReturnTypeImplTrait(func, idx);
                        let generics = generics(self.db.upcast(), func.into());
                        let type_args = if let Some(def) = self.resolver.generic_def() {
                            TypeArgs::type_params(self.db.upcast(), def)
                        } else {
                            TypeArgs::empty()
                        };
                        Type::Opaque(OpaqueType { opaque_ty_id, arguments: type_args })
                    }
                    ImplTraitLoweringMode::Param => {
                        let idx = self.impl_trait_counter.get();
                        // FIXME we're probably doing something wrong here
                        self.impl_trait_counter.set(idx + count_impl_traits(type_ref) as u16);
                        if let Some(def) = self.resolver.generic_def() {
                            let generics = generics(self.db.upcast(), def);
                            let param = generics
                                .iter()
                                .filter(|(_, data)| {
                                    data.provenance == TypeParamProvenance::ArgumentImplTrait
                                })
                                .nth(idx as usize)
                                .map_or(Type::Error, |(id, _)| Type::Param(id));
                            param
                        } else {
                            panic!("argument impl trait lowering without generic context")
                        }
                    }
                    ImplTraitLoweringMode::Disallowed => {
                        // FIXME: report error
                        Type::Error
                    }
                }
            }
            TypeRef::Error => Type::Error,
        };
        (ty, res)
    }

    /// This is only for `generic_bounds_for_param`, where we can't just
    /// lower the self types of the predicates since that could lead to cycles.
    /// So we just check here if the `type_ref` resolves to a generic param, and which.
    fn lower_only_param(&self, type_ref: &TypeRef) -> Option<TypeParamId> {
        let path = match type_ref {
            TypeRef::Path(path) => path,
            _ => return None,
        };
        if path.type_anchor().is_some() {
            return None;
        }
        if path.segments().len() > 1 {
            return None;
        }
        let resolution =
            match self.resolver.resolve_path_in_type_ns(self.db.upcast(), path.mod_path()) {
                Some((it, None)) => it,
                _ => return None,
            };
        if let TypeNs::GenericParam(param_id) = resolution {
            Some(param_id)
        } else {
            None
        }
    }

    pub(crate) fn lower_path(&self, path: &Path) -> (Type, Option<TypeNs>) {
        // Resolve the path (in type namespace)
        if let Some(type_ref) = path.type_anchor() {
            let (ty, res) = self.lower_type_ext(&type_ref);
            return self.lower_type_relative_path(ty, res, path.segments());
        }
        let (resolution, remaining_index) =
            match self.resolver.resolve_path_in_type_ns(self.db.upcast(), path.mod_path()) {
                Some(it) => it,
                None => return (Type::Error, None),
            };
        let (resolved_segment, remaining_segments) = match remaining_index {
            None => (
                path.segments().last().expect("resolved path has at least one element"),
                PathSegments::EMPTY,
            ),
            Some(i) => (path.segments().get(i - 1).unwrap(), path.segments().skip(i)),
        };
        self.lower_partly_resolved_hir_path(resolution, resolved_segment, remaining_segments, false)
    }

    pub(crate) fn lower_type_relative_path(
        &self,
        relative_to: Type,
        // We need the original resolution to lower `Self::AssocTy` correctly
        res: Option<TypeNs>,
        remaining_segments: PathSegments<'_>,
    ) -> (Type, Option<TypeNs>) {
        if remaining_segments.len() == 1 {
            // resolve unselected assoc types
            let segment = remaining_segments.first().unwrap();
            (self.select_associated_type(relative_to, res, segment), None)
        } else if remaining_segments.len() > 1 {
            // FIXME report error (ambiguous associated type)
            (Type::Error, None)
        } else {
            (relative_to, res)
        }
    }

    pub(crate) fn lower_partly_resolved_hir_path(
        &self,
        resolution: TypeNs,
        resolved_segment: PathSegment<'_>,
        remaining_segments: PathSegments<'_>,
        infer_args: bool,
    ) -> (Type, Option<TypeNs>) {
        let ty = match resolution {
            TypeNs::TraitId(trait_) => {
                let ty = if remaining_segments.len() == 1 {
                    let segment = remaining_segments.first().unwrap();
                    let arguments =
                        self.args_from_path_segment(resolved_segment, trait_.into(), false, true);
                    let trait_bound = TraitBound {
                        trait_,
                        arguments: arguments.iter().skip(1).cloned().collect(),
                    };
                    let associated_ty = associated_type_by_name_including_super_traits(
                        self.db,
                        trait_bound,
                        &segment.name,
                    );
                    match associated_ty {
                        Some((trait_bound, associated_ty)) => {
                            let arguments = iter::once(arguments[0].clone())
                                .chain(trait_bound.arguments.iter().cloned())
                                .collect();
                            // FIXME handle type parameters on the segment
                            Type::Projection(ProjectionType { associated_ty, arguments })
                        }
                        None => {
                            // FIXME: report error (associated type not found)
                            Type::Error
                        }
                    }
                } else if remaining_segments.len() > 1 {
                    // FIXME report error (ambiguous associated type)
                    Type::Error
                } else {
                    let bounds = self.lower_resolved_path_to_bounds(trait_, resolved_segment);
                    // FIXME forbid self type
                    Type::Dyn(bounds.into_boxed_slice().into())
                };
                return (ty, None);
            }
            TypeNs::GenericParam(param_id) => Type::Param(param_id),
            TypeNs::SelfType(impl_id) => self.db.impl_self_type(impl_id),
            TypeNs::AdtSelfType(adt) => {
                let generics = generics(self.db.upcast(), adt.into());
                let arguments = TypeArgs::type_params_for_generics(&generics);
                Type::Apply(ApplicationType { name: TypeName::Adt(adt), arguments })
            }

            TypeNs::AdtId(it) => self.lower_path_inner(resolved_segment, it.into(), infer_args),
            TypeNs::BuiltinType(it) => {
                self.lower_path_inner(resolved_segment, it.into(), infer_args)
            }
            TypeNs::TypeAliasId(it) => {
                self.lower_path_inner(resolved_segment, it.into(), infer_args)
            }
            // FIXME: report error
            TypeNs::EnumVariantId(_) => return (Type::Error, None),
        };

        self.lower_type_relative_path(ty, Some(resolution), remaining_segments)
    }

    fn select_associated_type(
        &self,
        relative_to: Type,
        res: Option<TypeNs>,
        segment: PathSegment<'_>,
    ) -> Type {
        if let Some(res) = res {
            let ty = associated_type_shorthand_candidates(
                self.db,
                res,
                move |name, t, associated_ty| {
                    if name == segment.name {
                        let arguments = iter::once(relative_to.clone())
                            .chain(t.arguments.iter().cloned())
                            .collect();
                        // FIXME handle (forbid) type parameters on the segment
                        return Some(Type::Projection(ProjectionType { associated_ty, arguments }));
                    }

                    None
                },
            );

            ty.unwrap_or(Type::Error) // FIXME report error
        } else {
            // FIXME I think this can only happen if the self type is already error, but check
            Type::Error
        }
    }

    fn lower_path_inner(
        &self,
        segment: PathSegment<'_>,
        typable: TyDefId,
        infer_args: bool,
    ) -> Type {
        match typable {
            TyDefId::BuiltinType(builtin_type) => Type::simple(type_for_builtin(builtin_type)),
            TyDefId::AdtId(it) => {
                let args = self.args_from_path_segment(segment, it.into(), infer_args, true);
                Type::apply(TypeName::Adt(it), args)
            }
            TyDefId::TypeAliasId(it) => {
                let args = self.args_from_path_segment(segment, it.into(), infer_args, true);
                let generics = generics(self.db.upcast(), it.into());
                substitute(&generics, self.db.type_alias_type(it), args)
            }
        }
    }

    /// Collect generic arguments from a path into a `TypeArgs`. See also
    /// `create_substs_for_ast_path` and `def_to_ty` in rustc.
    pub(super) fn args_from_path(
        &self,
        path: &Path,
        // Note that we don't call `db.value_type(resolved)` here,
        // `ValueTyDefId` is just a convenient way to pass generics and
        // special-case enum variants
        resolved: ValueTyDefId,
        infer_args: bool,
    ) -> TypeArgs {
        let last = path.segments().last().expect("path should have at least one segment");
        let (segment, generic_def) = match resolved {
            ValueTyDefId::FunctionId(it) => (last, Some(it.into())),
            ValueTyDefId::StructId(it) => (last, Some(it.into())),
            ValueTyDefId::UnionId(it) => (last, Some(it.into())),
            ValueTyDefId::ConstId(it) => (last, Some(it.into())),
            ValueTyDefId::StaticId(_) => (last, None),
            ValueTyDefId::EnumVariantId(var) => {
                // the generic args for an enum variant may be either specified
                // on the segment referring to the enum, or on the segment
                // referring to the variant. So `Option::<T>::None` and
                // `Option::None::<T>` are both allowed (though the former is
                // preferred). See also `def_ids_for_path_segments` in rustc.
                let len = path.segments().len();
                let penultimate = if len >= 2 { path.segments().get(len - 2) } else { None };
                let segment = match penultimate {
                    Some(segment) if segment.args_and_bindings.is_some() => segment,
                    _ => last,
                };
                (segment, Some(var.parent.into()))
            }
        };
        if let Some(generic_def) = generic_def {
            self.args_from_path_segment(segment, generic_def, infer_args, true)
        } else {
            // FIXME forbid type args
            TypeArgs::empty()
        }
    }

    fn args_from_path_segment(
        &self,
        segment: PathSegment<'_>,
        generic_def: GenericDefId,
        infer_args: bool,
        include_self: bool,
    ) -> TypeArgs {
        let mut substs = Vec::new();
        let def_generics = generics(self.db.upcast(), generic_def);

        let (parent_params, actual_self_params, type_params, impl_trait_params) =
            def_generics.provenance_split();
        let self_params = if include_self { actual_self_params } else { 0 };
        let total_len = parent_params + self_params + type_params + impl_trait_params;

        substs.extend(iter::repeat(Type::Infer).take(parent_params));

        let mut had_explicit_args = false;

        if let Some(generic_args) = &segment.args_and_bindings {
            if !generic_args.has_self_type {
                substs.extend(iter::repeat(Type::Infer).take(self_params));
            }
            // FIXME: if !include_self, has_self_type should be an error
            let expected_num =
                if generic_args.has_self_type { self_params + type_params } else { type_params };
            let skip = if generic_args.has_self_type && self_params == 0 { 1 } else { 0 };
            // if args are provided, it should be all of them, but we can't rely on that
            for arg in
                generic_args.args.iter().filter(|arg| arg.is_type()).skip(skip).take(expected_num)
            {
                match arg {
                    GenericArg::Type(type_ref) => {
                        had_explicit_args = true;
                        let ty = self.lower_type(type_ref);
                        substs.push(ty);
                    }
                    GenericArg::Lifetime(_) => {}
                }
            }
        }

        // handle defaults. In expression or pattern path segments without
        // explicitly specified type arguments, missing type arguments are inferred
        // (i.e. defaults aren't used).
        if !infer_args || had_explicit_args {
            let default_substs = self.db.generic_defaults_2(generic_def);
            let ignored_self_params = if !include_self { actual_self_params } else { 0 };
            assert_eq!(total_len + ignored_self_params, default_substs.len());

            let skip = ignored_self_params + substs.len();

            for default_ty in default_substs.iter().skip(skip) {
                // each default can depend on the previous parameters
                let substs_so_far = TypeArgs(substs.clone().into());
                substs.push(substitute(&def_generics, default_ty.clone(), substs_so_far));
            }
        }

        // add placeholders for args that were not provided
        // FIXME: emit diagnostics && error in contexts where this is not allowed
        for _ in substs.len()..total_len {
            substs.push(Type::Infer);
        }
        assert_eq!(substs.len(), total_len);

        TypeArgs(substs.into())
    }

    pub fn lower_bound(&self, bound: &TypeBound) -> SmallVec<[Bound; 1]> {
        match bound {
            TypeBound::Path(path) => self.lower_path_to_bounds(path),
            TypeBound::Lifetime(_) => SmallVec::new(),
            TypeBound::Error => SmallVec::from_buf([Bound::Error]),
        }
    }

    pub fn lower_type_ref_to_trait(&self, type_ref: &TypeRef) -> Option<TraitBound> {
        let path = match type_ref {
            TypeRef::Path(path) => path,
            _ => {
                // FIXME report error
                return None;
            }
        };
        let bounds = self.lower_path_to_bounds(path);
        let trait_bound = match &bounds[0] {
            Bound::Trait(trait_bound) => trait_bound.clone(),
            _ => {
                // FIXME report error, if this can actually happen
                return None;
            }
        };
        // FIXME report errors about additional bounds
        Some(trait_bound)
    }

    fn lower_path_to_bounds(&self, path: &Path) -> SmallVec<[Bound; 1]> {
        let trait_ =
            match self.resolver.resolve_path_in_type_ns_fully(self.db.upcast(), path.mod_path()) {
                Some(TypeNs::TraitId(tr)) => tr,
                _ => {
                    // FIXME report error
                    return SmallVec::from_buf([Bound::Error]);
                }
            };
        let segment = path.segments().last().expect("path should have at least one segment");
        self.lower_resolved_path_to_bounds(trait_, segment)
    }

    fn lower_resolved_path_to_bounds(
        &self,
        trait_: TraitId,
        segment: PathSegment<'_>,
    ) -> SmallVec<[Bound; 1]> {
        let arguments = self.args_from_path_segment(segment.clone(), trait_.into(), false, false);
        let trait_bound = TraitBound { trait_, arguments };
        let mut result = SmallVec::from_buf([Bound::Trait(trait_bound.clone())]);
        self.lower_assoc_type_bindings(&trait_bound, segment, &mut result);
        result
    }

    fn lower_assoc_type_bindings(
        &self,
        trait_bound: &TraitBound,
        segment: PathSegment,
        acc: &mut SmallVec<[Bound; 1]>,
    ) {
        let bindings = match segment.args_and_bindings {
            Some(a_and_b) => &a_and_b.bindings,
            None => return,
        };
        for binding in bindings {
            let found = associated_type_by_name_including_super_traits(
                self.db,
                trait_bound.clone(),
                &binding.name,
            );
            let (super_trait_bound, associated_ty) = match found {
                None => return,
                Some(t) => t,
            };
            if let Some(type_ref) = &binding.type_ref {
                let ty = self.lower_type(type_ref);
                acc.push(Bound::AssocTypeBinding(AssocTypeBinding {
                    associated_ty,
                    arguments: super_trait_bound.arguments,
                    ty,
                }));
            }

            for bound in &binding.bounds {
                // TODO these have a different self parameter, so they need to be modeled differently
                // TODO also add a test for these
                // acc.extend(self.lower_bound(bound));
            }
        }
    }
}

fn type_for_builtin(def: BuiltinType) -> TypeName {
    match def {
        BuiltinType::Char => TypeName::Char,
        BuiltinType::Bool => TypeName::Bool,
        BuiltinType::Str => TypeName::Str,
        BuiltinType::Int(t) => TypeName::Int(IntTy::from(t).into()),
        BuiltinType::Float(t) => TypeName::Float(FloatTy::from(t).into()),
    }
}

fn count_impl_traits(type_ref: &TypeRef) -> usize {
    let mut count = 0;
    type_ref.walk(&mut |type_ref| {
        if matches!(type_ref, TypeRef::ImplTrait(_)) {
            count += 1;
        }
    });
    count
}

fn direct_super_trait_bounds(db: &dyn HirDatabase, trait_bound: &TraitBound) -> Vec<TraitBound> {
    // returning the iterator directly doesn't easily work because of
    // lifetime problems, but since there usually shouldn't be more than a
    // few direct traits this should be fine (we could even use some kind of
    // SmallVec if performance is a concern)
    let generics = generics(db.upcast(), trait_bound.trait_.into());
    let generic_params = db.generic_params(trait_bound.trait_.into());
    let trait_self = match generic_params.find_trait_self_param() {
        Some(p) => TypeParamId { parent: trait_bound.trait_.into(), local_id: p },
        None => return Vec::new(),
    };
    db.generic_bounds_for_param(trait_self)
        .iter()
        .filter_map(|bound| match bound {
            Bound::Trait(tr) => Some(tr.clone()),
            _ => None,
        })
        .map(|bound| substitute(&generics, bound, trait_bound.arguments.clone()))
        .collect()
}

/// Given a trait bound (`Self: Trait`), builds all the implied trait bounds for
/// super traits. The original trait ref will be included. So the difference to
/// `all_super_traits` is that we keep track of type parameters; for example if
/// we have `Self: Trait<u32, i32>` and `Trait<T, U>: OtherTrait<U>` we'll get
/// `Self: OtherTrait<i32>`.
pub(super) fn all_super_trait_bounds(
    db: &dyn HirDatabase,
    trait_bound: TraitBound,
) -> Vec<TraitBound> {
    // we need to take care a bit here to avoid infinite loops in case of cycles
    // (i.e. if we have `trait A: B; trait B: A;`)
    let mut result = vec![trait_bound];
    let mut i = 0;
    while i < result.len() {
        let t = &result[i];
        // yeah this is quadratic, but trait hierarchies should be flat
        // enough that this doesn't matter
        for tt in direct_super_trait_bounds(db, t) {
            if !result.iter().any(|tr| tr.trait_ == tt.trait_) {
                result.push(tt);
            }
        }
        i += 1;
    }
    result
}

pub(super) fn associated_type_by_name_including_super_traits(
    db: &dyn HirDatabase,
    trait_bound: TraitBound,
    name: &Name,
) -> Option<(TraitBound, TypeAliasId)> {
    all_super_trait_bounds(db, trait_bound).into_iter().find_map(|t| {
        let assoc_type = db.trait_data(t.trait_).associated_type_by_name(name)?;
        Some((t, assoc_type))
    })
}

pub fn associated_type_shorthand_candidates<R>(
    db: &dyn HirDatabase,
    res: TypeNs,
    mut cb: impl FnMut(&Name, &TraitBound, TypeAliasId) -> Option<R>,
) -> Option<R> {
    let traits_from_env: Vec<_> = match res {
        TypeNs::SelfType(impl_id) => match db.impl_trait_2(impl_id) {
            None => return None,
            Some(trait_bound) => vec![trait_bound],
        },
        TypeNs::GenericParam(param_id) => {
            let predicates = db.generic_bounds_for_param(param_id);
            let mut traits_: Vec<_> = predicates
                .iter()
                .filter_map(|pred| match &pred {
                    Bound::Trait(tr) => Some(tr.clone()),
                    _ => None,
                })
                .collect();
            // Handle `Self::Type` referring to own associated type in trait definitions
            if let GenericDefId::TraitId(trait_id) = param_id.parent {
                let generics = generics(db.upcast(), trait_id.into());
                if generics.params.types[param_id.local_id].provenance
                    == TypeParamProvenance::TraitSelf
                {
                    let trait_bounds = TraitBound {
                        trait_: trait_id,
                        arguments: TypeArgs::type_params_for_generics(&generics),
                    };
                    traits_.push(trait_bounds);
                }
            }
            traits_
        }
        _ => return None,
    };

    for t in traits_from_env.into_iter().flat_map(move |t| all_super_trait_bounds(db, t)) {
        let data = db.trait_data(t.trait_);

        for (name, assoc_id) in &data.items {
            match assoc_id {
                AssocItemId::TypeAliasId(alias) => {
                    if let Some(result) = cb(name, &t, *alias) {
                        return Some(result);
                    }
                }
                AssocItemId::FunctionId(_) | AssocItemId::ConstId(_) => {}
            }
        }
    }

    None
}

pub(crate) fn type_alias_type_query(db: &dyn HirDatabase, t: TypeAliasId) -> Type {
    let generics = generics(db.upcast(), t.into());
    let resolver = t.resolver(db.upcast());
    let ctx = Context::new(db, &resolver);
    let data = db.type_alias_data(t);

    if data.is_extern {
        let args = TypeArgs::type_params_for_generics(&generics);
        Type::apply(TypeName::ForeignType(t), args)
    } else {
        let type_ref = &data.type_ref;
        ctx.lower_type(type_ref.as_ref().unwrap_or(&TypeRef::Error))
    }
}
pub(crate) fn type_alias_type_recover(
    db: &dyn HirDatabase,
    _cycle: &[String],
    _def: &TypeAliasId,
) -> Type {
    // FIXME report cycle error
    Type::Error
}

pub(crate) fn impl_self_type_query(db: &dyn HirDatabase, impl_id: ImplId) -> Type {
    let impl_data = db.impl_data(impl_id);
    let resolver = impl_id.resolver(db.upcast());
    let generics = generics(db.upcast(), impl_id.into());
    let ctx = Context::new(db, &resolver);
    ctx.lower_type(&impl_data.target_type)
}
pub(crate) fn impl_self_type_recover(
    db: &dyn HirDatabase,
    _cycle: &[String],
    def: &ImplId,
) -> Type {
    // FIXME report cycle error
    Type::Error
}

pub(crate) fn impl_trait_query(db: &dyn HirDatabase, impl_id: ImplId) -> Option<TraitBound> {
    let impl_data = db.impl_data(impl_id);
    let resolver = impl_id.resolver(db.upcast());
    let ctx = Context::new(db, &resolver);
    let target_trait = impl_data.target_trait.as_ref()?;
    ctx.lower_type_ref_to_trait(&target_trait)
}

pub(crate) fn generic_bounds_for_param_query(
    db: &dyn HirDatabase,
    param_id: TypeParamId,
) -> Arc<[Bound]> {
    let resolver = param_id.parent.resolver(db.upcast());
    let ctx = Context::new(db, &resolver);
    let generics = generics(db.upcast(), param_id.parent);
    resolver
        .where_predicates_in_scope()
        // we have to filter out all other predicates *first*, before attempting to lower them
        .filter(|pred| match &pred {
            WherePredicate::ForLifetime { target, .. }
            | WherePredicate::TypeBound { target, .. } => match target {
                WherePredicateTypeTarget::TypeRef(type_ref) => {
                    ctx.lower_only_param(type_ref) == Some(param_id)
                }
                WherePredicateTypeTarget::TypeParam(local_id) => *local_id == param_id.local_id,
            },
            WherePredicate::Lifetime { .. } => false,
        })
        .flat_map(|pred| match pred {
            WherePredicate::TypeBound { bound, .. } | WherePredicate::ForLifetime { bound, .. } => {
                ctx.lower_bound(bound)
            }
            WherePredicate::Lifetime { target, bound } => {
                unreachable!()
            }
        })
        .collect()
}
pub(crate) fn generic_bounds_for_param_recover(
    db: &dyn HirDatabase,
    _cycle: &[String],
    param_id: &TypeParamId,
) -> Arc<[Bound]> {
    // FIXME report cycle error
    Arc::new([])
}

pub(crate) fn generic_bounds_query(db: &dyn HirDatabase, def: GenericDefId) -> Arc<[WhereClause]> {
    let resolver = def.resolver(db.upcast());
    let ctx = Context::new(db, &resolver);
    let generics = generics(db.upcast(), def);
    let mut acc = Vec::new();
    let lower_target = |target: &WherePredicateTypeTarget| match target {
        WherePredicateTypeTarget::TypeRef(type_ref) => ctx.lower_type(type_ref),
        WherePredicateTypeTarget::TypeParam(local_id) => {
            Type::Param(TypeParamId { parent: def, local_id: *local_id })
        }
    };
    for pred in resolver.where_predicates_in_scope() {
        match pred {
            WherePredicate::TypeBound { target, bound } => {
                let ty = lower_target(target);
                ctx.lower_bound(&bound)
                    .into_iter()
                    .for_each(|bound| acc.push(WhereClause { bound, ty: ty.clone() }));
            }
            WherePredicate::Lifetime { target, bound } => {}
            WherePredicate::ForLifetime { lifetimes, target, bound } => {
                let ty = lower_target(target);
                ctx.lower_bound(&bound)
                    .into_iter()
                    .for_each(|bound| acc.push(WhereClause { bound, ty: ty.clone() }));
            }
        }
    }
    acc.into()
}

pub(crate) fn generic_defaults_query(db: &dyn HirDatabase, def: GenericDefId) -> Arc<[Type]> {
    let resolver = def.resolver(db.upcast());
    let ctx = Context::new(db, &resolver);
    let generic_params = generics(db.upcast(), def);

    let defaults = generic_params
        .iter()
        .enumerate()
        .map(|(idx, (_, p))| {
            let mut ty = p.default.as_ref().map_or(Type::Infer, |t| ctx.lower_type(t));

            // Each default can only refer to previous parameters.
            ty.walk_mut(&mut |ty| match ty {
                Type::Param(param_id) => {
                    let param_idx =
                        generic_params.param_idx(*param_id).expect("generic param without index");
                    if param_idx >= idx {
                        // type variable default referring to parameter coming
                        // after it. This is forbidden (FIXME: report
                        // diagnostic)
                        *ty = Type::Error;
                    }
                }
                _ => {}
            });

            ty
        })
        .collect();

    defaults
}

pub(crate) fn function_signature_query(db: &dyn HirDatabase, f: FunctionId) -> LoweredFn {
    let data = db.function_data(f);
    let resolver = f.resolver(db.upcast());
    let ctx_param = Context::new(db, &resolver).with_impl_trait_mode(ImplTraitLoweringMode::Param);
    let params = data.params.iter().map(|tr| ctx_param.lower_type(tr)).collect::<Vec<_>>();
    let ctx_ret = ctx_param.with_impl_trait_mode(ImplTraitLoweringMode::Opaque);
    let ret = ctx_ret.lower_type(&data.ret_type);
    let sig = FnSig::from_params_and_return(params, ret, data.is_varargs);
    let impl_traits = ctx_ret.opaque_type_data.into_inner().into();
    LoweredFn { sig, impl_traits }
}

pub(crate) fn callable_item_signature_query(db: &dyn HirDatabase, def: CallableDefId) -> FnSig {
    match def {
        CallableDefId::FunctionId(f) => db.function_signature(f).sig,
        CallableDefId::StructId(s) => fn_sig_for_struct_constructor(db, s),
        CallableDefId::EnumVariantId(e) => fn_sig_for_enum_variant_constructor(db, e),
    }
}

fn fn_sig_for_struct_constructor(db: &dyn HirDatabase, def: StructId) -> FnSig {
    let struct_data = db.struct_data(def);
    let fields = struct_data.variant_data.fields();
    let resolver = def.resolver(db.upcast());
    let ctx = Context::new(db, &resolver).with_impl_trait_mode(ImplTraitLoweringMode::Param);
    let params =
        fields.iter().map(|(_, field)| ctx.lower_type(&field.type_ref)).collect::<Vec<_>>();
    let args = TypeArgs::type_params(db.upcast(), def.into());
    let ret = Type::apply(TypeName::Adt(def.into()), args);
    FnSig::from_params_and_return(params, ret, false)
}

fn fn_sig_for_enum_variant_constructor(db: &dyn HirDatabase, def: EnumVariantId) -> FnSig {
    let enum_data = db.enum_data(def.parent);
    let var_data = &enum_data.variants[def.local_id];
    let fields = var_data.variant_data.fields();
    let resolver = def.parent.resolver(db.upcast());
    let ctx = Context::new(db, &resolver).with_impl_trait_mode(ImplTraitLoweringMode::Param);
    let params =
        fields.iter().map(|(_, field)| ctx.lower_type(&field.type_ref)).collect::<Vec<_>>();
    let args = TypeArgs::type_params(db.upcast(), def.parent.into());
    let ret = Type::apply(TypeName::Adt(def.parent.into()), args);
    FnSig::from_params_and_return(params, ret, false)
}

/// Build the declared type of a const.
pub(crate) fn const_type_query(db: &dyn HirDatabase, def: ConstId) -> Type {
    let data = db.const_data(def);
    let resolver = def.resolver(db.upcast());
    let ctx = Context::new(db, &resolver);
    ctx.lower_type(&data.type_ref)
}

/// Build the declared type of a static.
pub(crate) fn static_type_query(db: &dyn HirDatabase, def: StaticId) -> Type {
    let data = db.static_data(def);
    let resolver = def.resolver(db.upcast());
    let ctx = Context::new(db, &resolver);
    ctx.lower_type(&data.type_ref)
}

/// Build the declared type of a const param.
pub(crate) fn const_param_type_query(db: &dyn HirDatabase, def: ConstParamId) -> Type {
    let parent_data = db.generic_params(def.parent);
    let data = &parent_data.consts[def.local_id];
    let resolver = def.parent.resolver(db.upcast());
    let ctx = Context::new(db, &resolver);
    ctx.lower_type(&data.ty)
}
