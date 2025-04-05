use hir_def::{AssocItemId, TypeAliasId};
use rustc_next_trait_solver::delegate::SolverDelegate;
use rustc_type_ir::{
    UniverseIndex,
    inherent::Span as _,
    solve::{Certainty, NoSolution},
};

use crate::{TraitRefExt, db::HirDatabase};

use super::{
    Canonical, CanonicalVarInfo, CanonicalVarValues, Const, DbInterner, DbIr, ErrorGuaranteed,
    GenericArg, GenericArgs, ParamEnv, Predicate, SolverDefId, Span, Ty, UnevaluatedConst,
    infer::{DbInternerInferExt, InferCtxt, canonical::instantiate::CanonicalExt},
};

pub type Goal<'db, P> = rustc_type_ir::solve::Goal<DbInterner<'db>, P>;

pub(crate) struct SolverContext<'db>(pub(crate) InferCtxt<'db>);

impl<'db> std::ops::Deref for SolverContext<'db> {
    type Target = InferCtxt<'db>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'db> SolverDelegate for SolverContext<'db> {
    type Interner = DbInterner<'db>;
    type Infcx = InferCtxt<'db>;

    fn cx(&self) -> Self::Interner {
        self.0.interner
    }

    fn build_with_canonical<V>(
        cx: Self::Interner,
        canonical: &rustc_type_ir::CanonicalQueryInput<Self::Interner, V>,
    ) -> (Self, V, rustc_type_ir::CanonicalVarValues<Self::Interner>)
    where
        V: rustc_type_ir::TypeFoldable<Self::Interner>,
    {
        let (infcx, value, vars) = cx.infer_ctxt().build_with_canonical(Span::dummy(), canonical);
        (SolverContext(infcx), value, vars)
    }

    fn fresh_var_for_kind_with_span(
        &self,
        arg: <Self::Interner as rustc_type_ir::Interner>::GenericArg,
        span: <Self::Interner as rustc_type_ir::Interner>::Span,
    ) -> <Self::Interner as rustc_type_ir::Interner>::GenericArg {
        todo!()
    }

    fn leak_check(
        &self,
        max_input_universe: rustc_type_ir::UniverseIndex,
    ) -> Result<(), NoSolution> {
        Ok(())
    }

    fn well_formed_goals(
        &self,
        param_env: <Self::Interner as rustc_type_ir::Interner>::ParamEnv,
        arg: <Self::Interner as rustc_type_ir::Interner>::GenericArg,
    ) -> Option<
        Vec<
            rustc_type_ir::solve::Goal<
                Self::Interner,
                <Self::Interner as rustc_type_ir::Interner>::Predicate,
            >,
        >,
    > {
        todo!()
    }

    fn clone_opaque_types_for_query_response(
        &self,
    ) -> Vec<(
        rustc_type_ir::OpaqueTypeKey<Self::Interner>,
        <Self::Interner as rustc_type_ir::Interner>::Ty,
    )> {
        // FIXME
        vec![]
    }

    fn make_deduplicated_outlives_constraints(
        &self,
    ) -> Vec<
        rustc_type_ir::OutlivesPredicate<
            Self::Interner,
            <Self::Interner as rustc_type_ir::Interner>::GenericArg,
        >,
    > {
        // FIXME: add if we care about regions
        vec![]
    }

    fn instantiate_canonical<V>(
        &self,
        canonical: rustc_type_ir::Canonical<Self::Interner, V>,
        values: rustc_type_ir::CanonicalVarValues<Self::Interner>,
    ) -> V
    where
        V: rustc_type_ir::TypeFoldable<Self::Interner>,
    {
        canonical.instantiate(self.cx(), &values)
    }

    fn instantiate_canonical_var_with_infer(
        &self,
        cv_info: rustc_type_ir::CanonicalVarInfo<Self::Interner>,
        span: <Self::Interner as rustc_type_ir::Interner>::Span,
        universe_map: impl Fn(rustc_type_ir::UniverseIndex) -> rustc_type_ir::UniverseIndex,
    ) -> <Self::Interner as rustc_type_ir::Interner>::GenericArg {
        self.0.instantiate_canonical_var(Span::dummy(), cv_info, universe_map)
    }

    fn register_hidden_type_in_storage(
        &self,
        opaque_type_key: rustc_type_ir::OpaqueTypeKey<Self::Interner>,
        hidden_ty: <Self::Interner as rustc_type_ir::Interner>::Ty,
        span: <Self::Interner as rustc_type_ir::Interner>::Span,
    ) -> Option<<Self::Interner as rustc_type_ir::Interner>::Ty> {
        todo!()
    }

    fn add_item_bounds_for_hidden_type(
        &self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
        args: <Self::Interner as rustc_type_ir::Interner>::GenericArgs,
        param_env: <Self::Interner as rustc_type_ir::Interner>::ParamEnv,
        hidden_ty: <Self::Interner as rustc_type_ir::Interner>::Ty,
        goals: &mut Vec<
            rustc_type_ir::solve::Goal<
                Self::Interner,
                <Self::Interner as rustc_type_ir::Interner>::Predicate,
            >,
        >,
    ) {
        todo!()
    }

    fn reset_opaque_types(&self) {
        std::mem::take(&mut self.inner.borrow_mut().opaque_type_storage.opaque_types);
    }

    fn fetch_eligible_assoc_item(
        &self,
        goal_trait_ref: rustc_type_ir::TraitRef<Self::Interner>,
        trait_assoc_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
        impl_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> Result<Option<<Self::Interner as rustc_type_ir::Interner>::DefId>, ErrorGuaranteed> {
        let impl_id = match impl_def_id {
            SolverDefId::ImplId(id) => id,
            _ => panic!("Unexpected SolverDefId"),
        };
        let trait_assoc_id = match trait_assoc_def_id {
            SolverDefId::TypeAliasId(id) => id,
            _ => panic!("Unexpected SolverDefId"),
        };
        let trait_ref = self
            .0
            .interner
            .db()
            .impl_trait(impl_id)
            // ImplIds for impls where the trait ref can't be resolved should never reach solver
            .expect("invalid impl passed to next-solver")
            .into_value_and_skipped_binders()
            .0;
        let trait_ = trait_ref.hir_trait_id();
        let trait_data = self.0.interner.db().trait_items(trait_);
        let id =
            self.0.interner.db().impl_items(impl_id).items.iter().find_map(|item| -> Option<_> {
                match item {
                    (_, AssocItemId::TypeAliasId(type_alias)) => {
                        let name = &self.0.interner.db().type_alias_signature(*type_alias).name;
                        let found_trait_assoc_id = trait_data.associated_type_by_name(name)?;
                        (found_trait_assoc_id == trait_assoc_id).then_some(*type_alias)
                    }
                    _ => None,
                }
            });
        Ok(id.map(|id| SolverDefId::TypeAliasId(id)))
    }

    fn is_transmutable(
        &self,
        dst: <Self::Interner as rustc_type_ir::Interner>::Ty,
        src: <Self::Interner as rustc_type_ir::Interner>::Ty,
        assume: <Self::Interner as rustc_type_ir::Interner>::Const,
    ) -> Result<Certainty, NoSolution> {
        todo!()
    }

    fn evaluate_const(
        &self,
        param_env: <Self::Interner as rustc_type_ir::Interner>::ParamEnv,
        uv: rustc_type_ir::UnevaluatedConst<Self::Interner>,
    ) -> Option<<Self::Interner as rustc_type_ir::Interner>::Const> {
        todo!()
    }
}
