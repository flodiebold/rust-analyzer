//! Methods for lowering the HIR to types. There are two main cases here:
//!
//!  - Lowering a type reference like `&usize` or `Option<foo::bar::Baz>` to a
//!    type: The entry point for this is `Ty::from_hir`.
//!  - Building the type for an item: This happens through the `type_for_def` query.
//!
//! This usually involves resolving names, collecting generic arguments etc.
use std::{iter, sync::Arc};

use base_db::CrateId;
use hir_def::{
    builtin_type::BuiltinType,
    path::{GenericArg, Path, PathSegment},
    resolver::Resolver,
    type_ref::TypeRef,
    AdtId, AssocContainerId, ConstId, ConstParamId, EnumId, EnumVariantId, FunctionId,
    GenericDefId, HasModule, ImplId, LocalFieldId, Lookup, StaticId, StructId,
    TypeAliasId, TypeParamId, UnionId, VariantId,
};
use la_arena::ArenaMap;
use stdx::{always, impl_from};

use crate::{
    db::HirDatabase,
    infer::{instantiate_outside_inference, instantiate_outside_inference_local},
    utils::generics,
    Binders, DebruijnIndex, GenericPredicate, PolyFnSig,
    ReturnTypeImplTrait, ReturnTypeImplTraits, Substs, TraitEnvironment, TraitRef,
    Ty, TypeCtor, TypeWalk,
};

#[derive(Debug)]
pub struct TyLoweringContext<'a> {
    pub db: &'a dyn HirDatabase,
    pub resolver: &'a Resolver,
}

impl<'a> TyLoweringContext<'a> {
    pub fn new(db: &'a dyn HirDatabase, resolver: &'a Resolver) -> Self {
        Self { db, resolver }
    }
}

impl Ty {
    pub fn from_hir(ctx: &TyLoweringContext<'_>, type_ref: &TypeRef) -> Self {
        let lower_ctx = crate::hir::lower::Context::new(ctx.db, ctx.resolver);
        let typ = lower_ctx.lower_type(type_ref);
        instantiate_outside_inference_local(ctx.db, ctx.resolver.generic_def(), &typ)
    }

    /// Collect generic arguments from a path into a `Substs`. See also
    /// `create_substs_for_ast_path` and `def_to_ty` in rustc.
    pub(super) fn substs_from_path(
        ctx: &TyLoweringContext<'_>,
        path: &Path,
        // Note that we don't call `db.value_type(resolved)` here,
        // `ValueTyDefId` is just a convenient way to pass generics and
        // special-case enum variants
        resolved: ValueTyDefId,
        infer_args: bool,
    ) -> Substs {
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
        substs_from_path_segment(ctx, segment, generic_def, infer_args)
    }
}

fn substs_from_path_segment(
    ctx: &TyLoweringContext<'_>,
    segment: PathSegment<'_>,
    def_generic: Option<GenericDefId>,
    infer_args: bool,
) -> Substs {
    let mut substs = Vec::new();
    let def_generics = def_generic.map(|def| generics(ctx.db.upcast(), def));

    let (parent_params, self_params, type_params, impl_trait_params) =
        def_generics.map_or((0, 0, 0, 0), |g| g.provenance_split());
    let total_len = parent_params + self_params + type_params + impl_trait_params;

    substs.extend(iter::repeat(Ty::Unknown).take(parent_params));

    let mut had_explicit_type_args = false;

    if let Some(generic_args) = &segment.args_and_bindings {
        if !generic_args.has_self_type {
            substs.extend(iter::repeat(Ty::Unknown).take(self_params));
        }
        let expected_num =
            if generic_args.has_self_type { self_params + type_params } else { type_params };
        let skip = if generic_args.has_self_type && self_params == 0 { 1 } else { 0 };
        // if args are provided, it should be all of them, but we can't rely on that
        for arg in generic_args
            .args
            .iter()
            .filter(|arg| matches!(arg, GenericArg::Type(_)))
            .skip(skip)
            .take(expected_num)
        {
            match arg {
                GenericArg::Type(type_ref) => {
                    had_explicit_type_args = true;
                    let ty = Ty::from_hir(ctx, type_ref);
                    substs.push(ty);
                }
                GenericArg::Lifetime(_) => {}
            }
        }
    }

    // handle defaults. In expression or pattern path segments without
    // explicitly specified type arguments, missing type arguments are inferred
    // (i.e. defaults aren't used).
    if !infer_args || had_explicit_type_args {
        if let Some(def_generic) = def_generic {
            let defaults = ctx.db.generic_defaults(def_generic);
            assert_eq!(total_len, defaults.len());

            for default_ty in defaults.iter().skip(substs.len()) {
                // each default can depend on the previous parameters
                let substs_so_far = Substs(substs.clone().into());
                substs.push(default_ty.clone().subst(&substs_so_far));
            }
        }
    }

    // add placeholders for args that were not provided
    // FIXME: emit diagnostics in contexts where this is not allowed
    for _ in substs.len()..total_len {
        substs.push(Ty::Unknown);
    }
    assert_eq!(substs.len(), total_len);

    Substs(substs.into())
}

/// Build the signature of a callable item (function, struct or enum variant).
pub fn callable_item_sig(db: &dyn HirDatabase, def: CallableDefId) -> PolyFnSig {
    let sig = db.callable_item_signature_2(def);
    instantiate_outside_inference(db, def.into(), &sig)
}

/// Build the type of all specific fields of a struct or enum variant.
pub(crate) fn field_types_query(
    db: &dyn HirDatabase,
    variant_id: VariantId,
) -> Arc<ArenaMap<LocalFieldId, Binders<Ty>>> {
    let def = match variant_id {
        VariantId::StructId(it) => it.into(),
        VariantId::UnionId(it) => it.into(),
        VariantId::EnumVariantId(it) => it.parent.into(),
    };
    let field_types = db.field_types_2(variant_id);
    let mut res = ArenaMap::default();
    for (field_id, typ) in field_types.iter() {
        res.insert(field_id, instantiate_outside_inference(db, def, typ));
    }
    Arc::new(res)
}

/// This query exists only to be used when resolving short-hand associated types
/// like `T::Item`.
///
/// See the analogous query in rustc and its comment:
/// https://github.com/rust-lang/rust/blob/9150f844e2624eb013ec78ca08c1d416e6644026/src/librustc_typeck/astconv.rs#L46
/// This is a query mostly to handle cycles somewhat gracefully; e.g. the
/// following bounds are disallowed: `T: Foo<U::Item>, U: Foo<T::Item>`, but
/// these are fine: `T: Foo<U::Item>, U: Foo<()>`.
pub(crate) fn generic_predicates_for_param_query(
    db: &dyn HirDatabase,
    param_id: TypeParamId,
) -> Arc<[Binders<GenericPredicate>]> {
    // FIXME: slightly hacky, but only needed temporarily
    let bounds = db.generic_bounds_for_param(param_id);
    let param_typ = crate::hir::Type::Param(param_id);
    bounds
        .iter()
        .map(|b| {
            instantiate_outside_inference(
                db,
                param_id.parent,
                &crate::hir::WhereClause { ty: param_typ.clone(), bound: b.clone() },
            )
        })
        .collect()
}

impl TraitEnvironment {
    pub fn lower(db: &dyn HirDatabase, resolver: &Resolver) -> Arc<TraitEnvironment> {
        let mut predicates = Vec::new();

        if let Some(def) = resolver.generic_def() {
            let ctx = crate::hir::lower::Context::new(db, resolver);
            resolver
                .where_predicates_in_scope()
                .for_each(|pred| {
                    ctx.lower_where_predicate(def, pred, &mut |clause| predicates.push(instantiate_outside_inference_local(db, Some(def), &clause)));
                });
            let container: Option<AssocContainerId> = match def {
                // FIXME: is there a function for this?
                GenericDefId::FunctionId(f) => Some(f.lookup(db.upcast()).container),
                GenericDefId::AdtId(_) => None,
                GenericDefId::TraitId(_) => None,
                GenericDefId::TypeAliasId(t) => Some(t.lookup(db.upcast()).container),
                GenericDefId::ImplId(_) => None,
                GenericDefId::EnumVariantId(_) => None,
                GenericDefId::ConstId(c) => Some(c.lookup(db.upcast()).container),
            };
            if let Some(AssocContainerId::TraitId(trait_id)) = container {
                // add `Self: Trait<T1, T2, ...>` to the environment in trait
                // function default implementations (and hypothetical code
                // inside consts or type aliases)
                test_utils::mark::hit!(trait_self_implements_self);
                let substs = Substs::type_params(db, trait_id);
                let trait_ref = TraitRef { trait_: trait_id, substs };
                let pred = GenericPredicate::Implemented(trait_ref);

                predicates.push(pred);
            }
        }

        Arc::new(TraitEnvironment { predicates })
    }
}

/// Resolve the where clause(s) of an item with generics.
pub(crate) fn generic_predicates_query(
    db: &dyn HirDatabase,
    def: GenericDefId,
) -> Arc<[Binders<GenericPredicate>]> {
    let bounds = db.generic_bounds(def);
    bounds.iter().map(|b| instantiate_outside_inference(db, def, b)).collect()
}

/// Resolve the default type params from generics
pub(crate) fn generic_defaults_query(
    db: &dyn HirDatabase,
    def: GenericDefId,
) -> Arc<[Binders<Ty>]> {
    let defaults = db.generic_defaults_2(def);
    defaults
        .iter()
        .enumerate()
        .map(|(i, t)| instantiate_outside_inference(db, def.into(), t).truncate_vars(i))
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CallableDefId {
    FunctionId(FunctionId),
    StructId(StructId),
    EnumVariantId(EnumVariantId),
}
impl_from!(FunctionId, StructId, EnumVariantId for CallableDefId);

impl CallableDefId {
    pub fn krate(self, db: &dyn HirDatabase) -> CrateId {
        let db = db.upcast();
        match self {
            CallableDefId::FunctionId(f) => f.lookup(db).module(db),
            CallableDefId::StructId(s) => s.lookup(db).container.module(db),
            CallableDefId::EnumVariantId(e) => e.parent.lookup(db).container.module(db),
        }
        .krate()
    }
}

impl From<CallableDefId> for GenericDefId {
    fn from(def: CallableDefId) -> GenericDefId {
        match def {
            CallableDefId::FunctionId(f) => f.into(),
            CallableDefId::StructId(s) => s.into(),
            CallableDefId::EnumVariantId(e) => e.into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyDefId {
    BuiltinType(BuiltinType),
    AdtId(AdtId),
    TypeAliasId(TypeAliasId),
}
impl_from!(BuiltinType, AdtId(StructId, EnumId, UnionId), TypeAliasId for TyDefId);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValueTyDefId {
    FunctionId(FunctionId),
    StructId(StructId),
    UnionId(UnionId),
    EnumVariantId(EnumVariantId),
    ConstId(ConstId),
    StaticId(StaticId),
}
impl_from!(FunctionId, StructId, UnionId, EnumVariantId, ConstId, StaticId for ValueTyDefId);

/// Build the declared type of an item. This depends on the namespace; e.g. for
/// `struct Foo(usize)`, we have two types: The type of the struct itself, and
/// the constructor function `(usize) -> Foo` which lives in the values
/// namespace.
pub(crate) fn ty_query(db: &dyn HirDatabase, def: TyDefId) -> Binders<Ty> {
    match def {
        TyDefId::BuiltinType(it) => Binders::new(0, Ty::builtin(it)),
        TyDefId::AdtId(it) => {
            let db = db;
            let adt = it;
            let generics = generics(db.upcast(), adt.into());
            let substs = Substs::bound_vars(&generics, DebruijnIndex::INNERMOST);
            Binders::new(substs.len(), Ty::apply(TypeCtor::Adt(adt), substs))
        }
        TyDefId::TypeAliasId(it) => {
            let typ = db.type_alias_type(it);
            instantiate_outside_inference(db, it.into(), &typ)
        }
    }
}

pub(crate) fn impl_self_ty_query(db: &dyn HirDatabase, impl_id: ImplId) -> Binders<Ty> {
    let typ = db.impl_self_type(impl_id);
    instantiate_outside_inference(db, impl_id.into(), &typ)
}

pub(crate) fn impl_trait_query(db: &dyn HirDatabase, impl_id: ImplId) -> Option<Binders<TraitRef>> {
    let impl_trait = db.impl_trait_2(impl_id)?;
    let self_type = db.impl_self_type(impl_id);
    let trait_ref = instantiate_outside_inference(db, impl_id.into(), &(impl_trait, self_type))
        .map(|(bound, self_ty)| {
            // FIXME: I believe this shiftiness should go away when we're using Chalk's types
            bound
                .subst(&Substs::single(self_ty.shift_bound_vars(DebruijnIndex::ONE)))
                .shift_bound_vars_out(DebruijnIndex::ONE)
        });
    Some(trait_ref)
}

pub(crate) fn return_type_impl_traits(
    db: &dyn HirDatabase,
    def: hir_def::FunctionId,
) -> Option<Arc<Binders<ReturnTypeImplTraits>>> {
    let data = db.function_signature(def);
    let instantiated: Vec<_> = data
        .impl_traits
        .iter()
        .map(|bounds| instantiate_outside_inference(db, def.into(), &&bounds[..]))
        .collect();

    if instantiated.is_empty() {
        None
    } else {
        let num_binders = instantiated[0].num_binders;
        always!(instantiated.iter().all(|it| it.num_binders == num_binders));
        let impl_traits = instantiated
            .into_iter()
            .map(|it| ReturnTypeImplTrait {
                bounds: it.map(|v| {
                    v.into_iter()
                        .map(|b| {
                            always!(b.num_binders == 1);
                            b.value
                        })
                        .collect()
                }),
            })
            .collect();
        Some(Arc::new(Binders::new(num_binders, ReturnTypeImplTraits { impl_traits })))
    }
}

pub(crate) fn const_param_ty_query(db: &dyn HirDatabase, def: ConstParamId) -> Binders<Ty> {
    let typ = db.const_param_type(def);
    instantiate_outside_inference(db, def.parent.into(), &typ)
}
