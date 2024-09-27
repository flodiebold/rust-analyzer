use rustc_type_ir::{
    solve::{NoSolution, SolverMode},
    ConstVid, FloatVid, InferCtxtLike, IntVid, RegionVid, TyVid, UniverseIndex, Variance,
};

use crate::db::HirDatabase;

use super::{
    Binder, Const, DbInterner, DefId, DefiningOpaqueTypes, GenericArgs, Goal, ParamEnv, Predicate,
    Region, Ty,
};

pub type Canonical<T> = rustc_type_ir::Canonical<DbInterner, T>;
pub type CanonicalVarValues = rustc_type_ir::CanonicalVarValues<DbInterner>;
pub type CanonicalVarInfo = rustc_type_ir::CanonicalVarInfo<DbInterner>;

#[derive(Clone)]
pub(crate) struct InferenceTable<'db> {
    interner: DbInterner,
    pub(crate) db: &'db dyn HirDatabase,
    // unify: ena::unify::InPlaceUnificationTable<TyVid>,
    // vars: Vec<TyVid>,
    max_universe: UniverseIndex,
}

impl<'db> InferCtxtLike for InferenceTable<'db> {
    type Interner = DbInterner;

    fn cx(&self) -> Self::Interner {
        self.interner
    }

    fn solver_mode(&self) -> SolverMode {
        todo!()
    }

    fn universe(&self) -> UniverseIndex {
        todo!()
    }

    fn create_next_universe(&self) -> UniverseIndex {
        todo!()
    }

    fn universe_of_ty(&self, ty: TyVid) -> Option<UniverseIndex> {
        todo!()
    }

    fn universe_of_lt(&self, lt: RegionVid) -> Option<UniverseIndex> {
        todo!()
    }

    fn universe_of_ct(&self, ct: ConstVid) -> Option<UniverseIndex> {
        todo!()
    }

    fn root_ty_var(&self, var: TyVid) -> TyVid {
        todo!()
    }

    fn root_const_var(&self, var: ConstVid) -> ConstVid {
        todo!()
    }

    fn opportunistic_resolve_ty_var(&self, vid: TyVid) -> Ty {
        todo!()
    }

    fn opportunistic_resolve_int_var(&self, vid: IntVid) -> Ty {
        todo!()
    }

    fn opportunistic_resolve_float_var(&self, vid: FloatVid) -> Ty {
        todo!()
    }

    fn opportunistic_resolve_ct_var(&self, vid: ConstVid) -> Const {
        todo!()
    }

    fn opportunistic_resolve_effect_var(&self, vid: rustc_type_ir::EffectVid) -> Const {
        todo!()
    }

    fn opportunistic_resolve_lt_var(&self, vid: RegionVid) -> Region {
        todo!()
    }

    fn defining_opaque_types(&self) -> DefiningOpaqueTypes {
        todo!()
    }

    fn next_ty_infer(&self) -> Ty {
        todo!()
    }

    fn next_const_infer(&self) -> Const {
        todo!()
    }

    fn fresh_args_for_item(&self, def_id: DefId) -> GenericArgs {
        todo!()
    }

    fn instantiate_binder_with_infer<
        T: rustc_type_ir::fold::TypeFoldable<Self::Interner> + Copy,
    >(
        &self,
        value: Binder<T>,
    ) -> T {
        todo!()
    }

    fn enter_forall<T: rustc_type_ir::fold::TypeFoldable<Self::Interner> + Copy, U>(
        &self,
        value: Binder<T>,
        f: impl FnOnce(T) -> U,
    ) -> U {
        todo!()
    }

    fn relate<T: rustc_type_ir::relate::Relate<Self::Interner>>(
        &self,
        param_env: ParamEnv,
        lhs: T,
        variance: Variance,
        rhs: T,
    ) -> Result<Vec<Goal<Predicate>>, NoSolution> {
        todo!()
    }

    fn eq_structurally_relating_aliases<T: rustc_type_ir::relate::Relate<Self::Interner>>(
        &self,
        param_env: ParamEnv,
        lhs: T,
        rhs: T,
    ) -> Result<Vec<Goal<Predicate>>, NoSolution> {
        todo!()
    }

    fn shallow_resolve(&self, ty: Ty) -> Ty {
        todo!()
    }

    fn resolve_vars_if_possible<T>(&self, value: T) -> T
    where
        T: rustc_type_ir::fold::TypeFoldable<Self::Interner>,
    {
        todo!()
    }

    fn probe<T>(&self, probe: impl FnOnce() -> T) -> T {
        todo!()
    }

    fn sub_regions(&self, sub: Region, sup: Region) {
        todo!()
    }

    fn register_ty_outlives(&self, ty: Ty, r: Region) {
        todo!()
    }
}
