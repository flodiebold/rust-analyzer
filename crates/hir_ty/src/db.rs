//! FIXME: write short doc here

use std::sync::Arc;

use base_db::{impl_intern_key, salsa, CrateId, Upcast};
use hir_def::{
    db::DefDatabase, expr::ExprId, ConstId, ConstParamId, DefWithBodyId, FunctionId, GenericDefId,
    ImplId, LocalFieldId, StaticId, TypeAliasId, TypeParamId, VariantId,
};
use la_arena::ArenaMap;

use crate::{
    hir::{Bound, TraitBound, Type},
    method_resolution::{InherentImpls, TraitImpls},
    traits::chalk,
    Binders, CallableDefId, GenericPredicate, InferenceResult, OpaqueTyId, PolyFnSig,
    ReturnTypeImplTraits, TraitRef, Ty, TyDefId,
};
use hir_expand::name::Name;

#[salsa::query_group(HirDatabaseStorage)]
pub trait HirDatabase: DefDatabase + Upcast<dyn DefDatabase> {
    #[salsa::invoke(infer_wait)]
    #[salsa::transparent]
    fn infer(&self, def: DefWithBodyId) -> Arc<InferenceResult>;

    #[salsa::invoke(crate::infer::infer_query)]
    fn infer_query(&self, def: DefWithBodyId) -> Arc<InferenceResult>;

    #[salsa::invoke(crate::lower::ty_query)]
    fn ty(&self, def: TyDefId) -> Binders<Ty>;

    #[salsa::invoke(crate::hir::type_alias_type_query)]
    #[salsa::cycle(crate::hir::type_alias_type_recover)]
    fn type_alias_type(&self, def: TypeAliasId) -> Type;

    #[salsa::invoke(crate::lower::impl_self_ty_query)]
    fn impl_self_ty(&self, def: ImplId) -> Binders<Ty>;

    #[salsa::invoke(crate::hir::impl_self_type_query)]
    #[salsa::cycle(crate::hir::impl_self_type_recover)]
    fn impl_self_type(&self, def: ImplId) -> Type;

    #[salsa::invoke(crate::hir::lower::const_param_type_query)]
    fn const_param_type(&self, def: ConstParamId) -> Type;

    #[salsa::invoke(crate::hir::const_type_query)]
    fn const_type(&self, def: ConstId) -> Type;

    #[salsa::invoke(crate::hir::static_type_query)]
    fn static_type(&self, def: StaticId) -> Type;

    #[salsa::invoke(crate::lower::impl_trait_query)]
    fn impl_trait(&self, def: ImplId) -> Option<Binders<TraitRef>>;

    #[salsa::invoke(crate::hir::impl_trait_query)]
    fn impl_trait_2(&self, def: ImplId) -> Option<TraitBound>;

    #[salsa::invoke(crate::lower::field_types_query)]
    fn field_types(&self, var: VariantId) -> Arc<ArenaMap<LocalFieldId, Binders<Ty>>>;

    #[salsa::invoke(crate::hir::function_signature_query)]
    fn function_signature(&self, f: FunctionId) -> crate::hir::LoweredFn;

    #[salsa::invoke(crate::callable_item_sig)]
    fn callable_item_signature(&self, def: CallableDefId) -> PolyFnSig;

    #[salsa::invoke(crate::hir::callable_item_signature_query)]
    fn callable_item_signature_2(&self, def: CallableDefId) -> crate::hir::FnSig;

    #[salsa::invoke(crate::lower::return_type_impl_traits)]
    fn return_type_impl_traits(
        &self,
        def: FunctionId,
    ) -> Option<Arc<Binders<ReturnTypeImplTraits>>>;

    #[salsa::invoke(crate::lower::generic_predicates_for_param_query)]
    #[salsa::cycle(crate::lower::generic_predicates_for_param_recover)]
    fn generic_predicates_for_param(
        &self,
        param_id: TypeParamId,
    ) -> Arc<[Binders<GenericPredicate>]>;

    #[salsa::invoke(crate::hir::generic_bounds_for_param_query)]
    #[salsa::cycle(crate::hir::generic_bounds_for_param_recover)]
    fn generic_bounds_for_param(&self, param_id: TypeParamId) -> Arc<[Bound]>;

    #[salsa::invoke(crate::lower::generic_predicates_query)]
    fn generic_predicates(&self, def: GenericDefId) -> Arc<[Binders<GenericPredicate>]>;

    #[salsa::invoke(crate::lower::generic_defaults_query)]
    fn generic_defaults(&self, def: GenericDefId) -> Arc<[Binders<Ty>]>;

    #[salsa::invoke(crate::hir::generic_defaults_query)]
    fn generic_defaults_2(&self, def: GenericDefId) -> Arc<[Type]>;

    #[salsa::invoke(InherentImpls::inherent_impls_in_crate_query)]
    fn inherent_impls_in_crate(&self, krate: CrateId) -> Arc<InherentImpls>;

    #[salsa::invoke(TraitImpls::trait_impls_in_crate_query)]
    fn trait_impls_in_crate(&self, krate: CrateId) -> Arc<TraitImpls>;

    #[salsa::invoke(TraitImpls::trait_impls_in_deps_query)]
    fn trait_impls_in_deps(&self, krate: CrateId) -> Arc<TraitImpls>;

    // Interned IDs for Chalk integration
    #[salsa::interned]
    fn intern_callable_def(&self, callable_def: CallableDefId) -> InternedCallableDefId;
    #[salsa::interned]
    fn intern_type_param_id(&self, param_id: TypeParamId) -> GlobalTypeParamId;
    #[salsa::interned]
    fn intern_impl_trait_id(&self, id: OpaqueTyId) -> InternedOpaqueTyId;
    #[salsa::interned]
    fn intern_closure(&self, id: (DefWithBodyId, ExprId)) -> ClosureId;

    #[salsa::invoke(chalk::associated_ty_data_query)]
    fn associated_ty_data(&self, id: chalk::AssocTypeId) -> Arc<chalk::AssociatedTyDatum>;

    #[salsa::invoke(chalk::trait_datum_query)]
    fn trait_datum(&self, krate: CrateId, trait_id: chalk::TraitId) -> Arc<chalk::TraitDatum>;

    #[salsa::invoke(chalk::struct_datum_query)]
    fn struct_datum(&self, krate: CrateId, struct_id: chalk::AdtId) -> Arc<chalk::StructDatum>;

    #[salsa::invoke(crate::traits::chalk::impl_datum_query)]
    fn impl_datum(&self, krate: CrateId, impl_id: chalk::ImplId) -> Arc<chalk::ImplDatum>;

    #[salsa::invoke(crate::traits::chalk::fn_def_datum_query)]
    fn fn_def_datum(&self, krate: CrateId, fn_def_id: chalk::FnDefId) -> Arc<chalk::FnDefDatum>;

    #[salsa::invoke(crate::traits::chalk::fn_def_variance_query)]
    fn fn_def_variance(&self, krate: CrateId, fn_def_id: chalk::FnDefId) -> chalk::Variances;

    #[salsa::invoke(crate::traits::chalk::adt_variance_query)]
    fn adt_variance(&self, krate: CrateId, adt_id: chalk::AdtId) -> chalk::Variances;

    #[salsa::invoke(crate::traits::chalk::associated_ty_value_query)]
    fn associated_ty_value(
        &self,
        krate: CrateId,
        id: chalk::AssociatedTyValueId,
    ) -> Arc<chalk::AssociatedTyValue>;

    #[salsa::invoke(crate::traits::trait_solve_query)]
    fn trait_solve(
        &self,
        krate: CrateId,
        goal: crate::Canonical<crate::InEnvironment<crate::Obligation>>,
    ) -> Option<crate::traits::Solution>;

    #[salsa::invoke(crate::traits::chalk::program_clauses_for_chalk_env_query)]
    fn program_clauses_for_chalk_env(
        &self,
        krate: CrateId,
        env: chalk_ir::Environment<chalk::Interner>,
    ) -> chalk_ir::ProgramClauses<chalk::Interner>;
}

fn infer_wait(db: &impl HirDatabase, def: DefWithBodyId) -> Arc<InferenceResult> {
    let _p = profile::span("infer:wait").detail(|| match def {
        DefWithBodyId::FunctionId(it) => db.function_data(it).name.to_string(),
        DefWithBodyId::StaticId(it) => {
            db.static_data(it).name.clone().unwrap_or_else(Name::missing).to_string()
        }
        DefWithBodyId::ConstId(it) => {
            db.const_data(it).name.clone().unwrap_or_else(Name::missing).to_string()
        }
    });
    db.infer_query(def)
}

#[test]
fn hir_database_is_object_safe() {
    fn _assert_object_safe(_: &dyn HirDatabase) {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GlobalTypeParamId(salsa::InternId);
impl_intern_key!(GlobalTypeParamId);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InternedOpaqueTyId(salsa::InternId);
impl_intern_key!(InternedOpaqueTyId);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClosureId(salsa::InternId);
impl_intern_key!(ClosureId);

/// This exists just for Chalk, because Chalk just has a single `FnDefId` where
/// we have different IDs for struct and enum variant constructors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct InternedCallableDefId(salsa::InternId);
impl_intern_key!(InternedCallableDefId);
