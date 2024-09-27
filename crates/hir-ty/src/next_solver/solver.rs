use rustc_next_trait_solver::delegate::SolverDelegate;
use rustc_type_ir::{
    solve::{Certainty, NoSolution, SolverMode},
    UniverseIndex,
};

use crate::db::HirDatabase;

use super::{
    infer::InferenceTable, Canonical, CanonicalVarInfo, CanonicalVarValues, Const, DbInterner,
    DefId, GenericArg, GenericArgs, OpaqueTypeKey, OutlivesPredicate, ParamEnv, Predicate, Span,
    TraitRef, Ty, UnevaluatedConst,
};

pub type Goal<P> = rustc_type_ir::solve::Goal<DbInterner, P>;

#[derive(Clone)]
pub(crate) struct SolverContext<'db> {
    table: InferenceTable<'db>,
}

impl<'db> std::ops::Deref for SolverContext<'db> {
    type Target = InferenceTable<'db>;

    fn deref(&self) -> &Self::Target {
        &self.table
    }
}

impl<'db> SolverDelegate for SolverContext<'db> {
    type Interner = DbInterner;

    type Span = Span;

    fn build_with_canonical<V>(
        cx: Self::Interner,
        solver_mode: SolverMode,
        canonical: &Canonical<V>,
    ) -> (Self, V, CanonicalVarValues)
    where
        V: rustc_type_ir::fold::TypeFoldable<Self::Interner>,
    {
        todo!()
    }

    fn fresh_var_for_kind_with_span(&self, arg: GenericArg, span: Self::Span) -> GenericArg {
        todo!()
    }

    fn leak_check(&self, max_input_universe: UniverseIndex) -> Result<(), NoSolution> {
        todo!()
    }

    fn try_const_eval_resolve(
        &self,
        param_env: ParamEnv,
        unevaluated: UnevaluatedConst,
    ) -> Option<Const> {
        todo!()
    }

    fn well_formed_goals(
        &self,
        param_env: ParamEnv,
        arg: GenericArg,
    ) -> Option<Vec<Goal<Predicate>>> {
        todo!()
    }

    fn clone_opaque_types_for_query_response(&self) -> Vec<(OpaqueTypeKey, Ty)> {
        todo!()
    }

    fn make_deduplicated_outlives_constraints(&self) -> Vec<OutlivesPredicate<GenericArg>> {
        todo!()
    }

    fn instantiate_canonical<V>(&self, canonical: Canonical<V>, values: CanonicalVarValues) -> V
    where
        V: rustc_type_ir::fold::TypeFoldable<Self::Interner>,
    {
        todo!()
    }

    fn instantiate_canonical_var_with_infer(
        &self,
        cv_info: CanonicalVarInfo,
        universe_map: impl Fn(UniverseIndex) -> UniverseIndex,
    ) -> GenericArg {
        todo!()
    }

    fn insert_hidden_type(
        &self,
        opaque_type_key: OpaqueTypeKey,
        param_env: ParamEnv,
        hidden_ty: Ty,
        goals: &mut Vec<Goal<Predicate>>,
    ) -> Result<(), NoSolution> {
        todo!()
    }

    fn add_item_bounds_for_hidden_type(
        &self,
        def_id: DefId,
        args: GenericArgs,
        param_env: ParamEnv,
        hidden_ty: Ty,
        goals: &mut Vec<Goal<Predicate>>,
    ) {
        todo!()
    }

    fn inject_new_hidden_type_unchecked(&self, key: OpaqueTypeKey, hidden_ty: Ty) {
        todo!()
    }

    fn reset_opaque_types(&self) {
        todo!()
    }

    fn fetch_eligible_assoc_item(
        &self,
        param_env: ParamEnv,
        goal_trait_ref: TraitRef,
        trait_assoc_def_id: DefId,
        impl_def_id: DefId,
    ) -> Result<Option<DefId>, NoSolution> {
        todo!()
    }

    fn is_transmutable(
        &self,
        param_env: ParamEnv,
        dst: Ty,
        src: Ty,
        assume: Const,
    ) -> Result<Certainty, NoSolution> {
        todo!()
    }
}
