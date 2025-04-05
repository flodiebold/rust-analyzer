use rustc_type_ir::{
    ConstVid, FloatVid, IntVid, RegionVid, TyVid, TypeFoldable, TypingMode, UniverseIndex,
    inherent::{Const as _, Span as _, Ty as _},
    relate::combine::PredicateEmittingRelation,
};

use crate::next_solver::{
    Binder, Const, DbInterner, DbIr, ErrorGuaranteed, GenericArgs, ParamEnv, Region, SolverDefId,
    Span, Ty,
};

///! Definition of `InferCtxtLike` from the librarified type layer.
use super::{
    BoundRegionConversionTime, InferCtxt, SubregionOrigin, relate::RelateResult,
    traits::ObligationCause,
};

impl<'db> rustc_type_ir::InferCtxtLike for InferCtxt<'db> {
    type Interner = DbInterner<'db>;

    fn cx(&self) -> DbInterner<'db> {
        self.interner
    }

    fn next_trait_solver(&self) -> bool {
        true
    }

    fn typing_mode(&self) -> TypingMode<DbInterner<'db>> {
        self.typing_mode()
    }

    fn universe(&self) -> UniverseIndex {
        self.universe()
    }

    fn create_next_universe(&self) -> UniverseIndex {
        self.create_next_universe()
    }

    fn universe_of_ty(&self, vid: TyVid) -> Option<UniverseIndex> {
        match self.probe_ty_var(vid) {
            Err(universe) => Some(universe),
            Ok(_) => None,
        }
    }

    fn universe_of_lt(&self, lt: RegionVid) -> Option<UniverseIndex> {
        match self.inner.borrow_mut().unwrap_region_constraints().probe_value(lt) {
            Err(universe) => Some(universe),
            Ok(_) => None,
        }
    }

    fn universe_of_ct(&self, ct: ConstVid) -> Option<UniverseIndex> {
        match self.probe_const_var(ct) {
            Err(universe) => Some(universe),
            Ok(_) => None,
        }
    }

    fn root_ty_var(&self, var: TyVid) -> TyVid {
        self.root_var(var)
    }

    fn root_const_var(&self, var: ConstVid) -> ConstVid {
        self.root_const_var(var)
    }

    fn opportunistic_resolve_ty_var(&self, vid: TyVid) -> Ty<'db> {
        match self.probe_ty_var(vid) {
            Ok(ty) => ty,
            Err(_) => Ty::new_var(self.interner, self.root_var(vid)),
        }
    }

    fn opportunistic_resolve_int_var(&self, vid: IntVid) -> Ty<'db> {
        self.opportunistic_resolve_int_var(vid)
    }

    fn opportunistic_resolve_float_var(&self, vid: FloatVid) -> Ty<'db> {
        self.opportunistic_resolve_float_var(vid)
    }

    fn opportunistic_resolve_ct_var(&self, vid: ConstVid) -> Const<'db> {
        match self.probe_const_var(vid) {
            Ok(ct) => ct,
            Err(_) => Const::new_var(self.interner, self.root_const_var(vid)),
        }
    }

    fn opportunistic_resolve_lt_var(&self, vid: RegionVid) -> Region<'db> {
        self.inner
            .borrow_mut()
            .unwrap_region_constraints()
            .opportunistic_resolve_var(self.interner, vid)
    }

    fn next_ty_infer(&self) -> Ty<'db> {
        self.next_ty_var(Span::dummy())
    }

    fn next_region_infer(&self) -> <Self::Interner as rustc_type_ir::Interner>::Region {
        self.next_region_var(super::RegionVariableOrigin::MiscVariable(Span::dummy()))
    }

    fn next_const_infer(&self) -> Const<'db> {
        self.next_const_var(Span::dummy())
    }

    fn fresh_args_for_item(&self, def_id: SolverDefId) -> GenericArgs<'db> {
        self.fresh_args_for_item(Span::dummy(), def_id)
    }

    fn instantiate_binder_with_infer<T: TypeFoldable<DbInterner<'db>> + Clone>(
        &self,
        value: Binder<'db, T>,
    ) -> T {
        self.instantiate_binder_with_fresh_vars(
            Span::dummy(),
            BoundRegionConversionTime::HigherRankedType,
            value,
        )
    }

    fn enter_forall<T: TypeFoldable<DbInterner<'db>> + Clone, U>(
        &self,
        value: Binder<'db, T>,
        f: impl FnOnce(T) -> U,
    ) -> U {
        self.enter_forall(value, f)
    }

    fn equate_ty_vids_raw(&self, a: rustc_type_ir::TyVid, b: rustc_type_ir::TyVid) {
        self.inner.borrow_mut().type_variables().equate(a, b);
    }

    fn equate_int_vids_raw(&self, a: rustc_type_ir::IntVid, b: rustc_type_ir::IntVid) {
        self.inner.borrow_mut().int_unification_table().union(a, b);
    }

    fn equate_float_vids_raw(&self, a: rustc_type_ir::FloatVid, b: rustc_type_ir::FloatVid) {
        self.inner.borrow_mut().float_unification_table().union(a, b);
    }

    fn equate_const_vids_raw(&self, a: rustc_type_ir::ConstVid, b: rustc_type_ir::ConstVid) {
        self.inner.borrow_mut().const_unification_table().union(a, b);
    }

    fn instantiate_ty_var_raw<R: PredicateEmittingRelation<Self>>(
        &self,
        relation: &mut R,
        target_is_expected: bool,
        target_vid: rustc_type_ir::TyVid,
        instantiation_variance: rustc_type_ir::Variance,
        source_ty: Ty<'db>,
    ) -> RelateResult<'db, ()> {
        self.instantiate_ty_var(
            relation,
            target_is_expected,
            target_vid,
            instantiation_variance,
            source_ty,
        )
    }

    fn instantiate_int_var_raw(
        &self,
        vid: rustc_type_ir::IntVid,
        value: rustc_type_ir::IntVarValue,
    ) {
        self.inner.borrow_mut().int_unification_table().union_value(vid, value);
    }

    fn instantiate_float_var_raw(
        &self,
        vid: rustc_type_ir::FloatVid,
        value: rustc_type_ir::FloatVarValue,
    ) {
        self.inner.borrow_mut().float_unification_table().union_value(vid, value);
    }

    fn instantiate_const_var_raw<R: PredicateEmittingRelation<Self>>(
        &self,
        relation: &mut R,
        target_is_expected: bool,
        target_vid: rustc_type_ir::ConstVid,
        source_ct: Const<'db>,
    ) -> RelateResult<'db, ()> {
        self.instantiate_const_var(relation, target_is_expected, target_vid, source_ct)
    }

    fn set_tainted_by_errors(&self, e: ErrorGuaranteed) {
        self.set_tainted_by_errors(e)
    }

    fn shallow_resolve(&self, ty: Ty<'db>) -> Ty<'db> {
        self.shallow_resolve(ty)
    }
    fn shallow_resolve_const(&self, ct: Const<'db>) -> Const<'db> {
        self.shallow_resolve_const(ct)
    }

    fn resolve_vars_if_possible<T>(&self, value: T) -> T
    where
        T: TypeFoldable<DbInterner<'db>>,
    {
        self.resolve_vars_if_possible(value)
    }

    fn probe<T>(&self, probe: impl FnOnce() -> T) -> T {
        self.probe(|_| probe())
    }

    fn sub_regions(&self, sub: Region<'db>, sup: Region<'db>, span: Span) {
        self.inner.borrow_mut().unwrap_region_constraints().make_subregion(
            SubregionOrigin::RelateRegionParamBound(span, None),
            sub,
            sup,
        );
    }

    fn equate_regions(&self, a: Region<'db>, b: Region<'db>, span: Span) {
        self.inner.borrow_mut().unwrap_region_constraints().make_eqregion(
            SubregionOrigin::RelateRegionParamBound(span, None),
            a,
            b,
        );
    }

    fn register_ty_outlives(&self, ty: Ty<'db>, r: Region<'db>, span: Span) {
        //self.register_region_obligation_with_cause(ty, r, &ObligationCause::dummy_with_span(Span::dummy()));
    }
}
