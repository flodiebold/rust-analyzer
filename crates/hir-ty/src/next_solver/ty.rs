use rustc_type_ir::{
    fold::{TypeFoldable, TypeSuperFoldable},
    inherent::{BoundVarLike, IntoKind, ParamLike, PlaceholderLike},
    relate::Relate,
    visit::{Flags, TypeSuperVisitable, TypeVisitable},
    TyKind,
};

use super::{with_db_out_of_thin_air, BoundTy, BoundVarKind, DbInterner, InternedTy, ParamTy, PlaceholderType, Ty, Tys};

impl IntoKind for Ty {
    type Kind = TyKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        with_db_out_of_thin_air(|db| db.lookup_intern_rustc_ty(self)).inner()
    }
}

impl TypeVisitable<DbInterner> for Ty {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeSuperVisitable<DbInterner> for Ty {
    fn super_visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for Ty {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl TypeSuperFoldable<DbInterner> for Ty {
    fn try_super_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl Relate<DbInterner> for Ty {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        todo!()
    }
}

impl Flags for Ty {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        todo!()
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        todo!()
    }
}

impl rustc_type_ir::inherent::Ty<DbInterner> for Ty {
    fn new_unit(interner: DbInterner) -> Self {
        todo!()
    }

    fn new_bool(interner: DbInterner) -> Self {
        interner.mk_ty(TyKind::Bool)
    }

    fn new_u8(interner: DbInterner) -> Self {
        interner.mk_ty(TyKind::Uint(rustc_type_ir::UintTy::U8))
    }

    fn new_usize(interner: DbInterner) -> Self {
        todo!()
    }

    fn new_infer(interner: DbInterner, var: rustc_type_ir::InferTy) -> Self {
        todo!()
    }

    fn new_var(interner: DbInterner, var: rustc_type_ir::TyVid) -> Self {
        todo!()
    }

    fn new_param(
        interner: DbInterner,
        param: <DbInterner as rustc_type_ir::Interner>::ParamTy,
    ) -> Self {
        todo!()
    }

    fn new_placeholder(
        interner: DbInterner,
        param: <DbInterner as rustc_type_ir::Interner>::PlaceholderTy,
    ) -> Self {
        todo!()
    }

    fn new_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: <DbInterner as rustc_type_ir::Interner>::BoundTy,
    ) -> Self {
        todo!()
    }

    fn new_anon_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: rustc_type_ir::BoundVar,
    ) -> Self {
        todo!()
    }

    fn new_alias(
        interner: DbInterner,
        kind: rustc_type_ir::AliasTyKind,
        alias_ty: rustc_type_ir::AliasTy<DbInterner>,
    ) -> Self {
        todo!()
    }

    fn new_error(
        interner: DbInterner,
        guar: <DbInterner as rustc_type_ir::Interner>::ErrorGuaranteed,
    ) -> Self {
        todo!()
    }

    fn new_adt(
        interner: DbInterner,
        adt_def: <DbInterner as rustc_type_ir::Interner>::AdtDef,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        todo!()
    }

    fn new_foreign(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
    ) -> Self {
        todo!()
    }

    fn new_dynamic(
        interner: DbInterner,
        preds: <DbInterner as rustc_type_ir::Interner>::BoundExistentialPredicates,
        region: <DbInterner as rustc_type_ir::Interner>::Region,
        kind: rustc_type_ir::DynKind,
    ) -> Self {
        todo!()
    }

    fn new_coroutine(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        todo!()
    }

    fn new_coroutine_closure(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        todo!()
    }

    fn new_closure(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        todo!()
    }

    fn new_coroutine_witness(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        todo!()
    }

    fn new_ptr(interner: DbInterner, ty: Self, mutbl: rustc_ast_ir::Mutability) -> Self {
        todo!()
    }

    fn new_ref(
        interner: DbInterner,
        region: <DbInterner as rustc_type_ir::Interner>::Region,
        ty: Self,
        mutbl: rustc_ast_ir::Mutability,
    ) -> Self {
        todo!()
    }

    fn new_array_with_const_len(
        interner: DbInterner,
        ty: Self,
        len: <DbInterner as rustc_type_ir::Interner>::Const,
    ) -> Self {
        todo!()
    }

    fn new_slice(interner: DbInterner, ty: Self) -> Self {
        todo!()
    }

    fn new_tup(interner: DbInterner, tys: &[<DbInterner as rustc_type_ir::Interner>::Ty]) -> Self {
        todo!()
    }

    fn new_tup_from_iter<It, T>(interner: DbInterner, iter: It) -> T::Output
    where
        It: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<Self, Self>,
    {
        todo!()
    }

    fn new_fn_def(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        todo!()
    }

    fn new_fn_ptr(
        interner: DbInterner,
        sig: rustc_type_ir::Binder<DbInterner, rustc_type_ir::FnSig<DbInterner>>,
    ) -> Self {
        todo!()
    }

    fn new_pat(
        interner: DbInterner,
        ty: Self,
        pat: <DbInterner as rustc_type_ir::Interner>::Pat,
    ) -> Self {
        todo!()
    }

    fn tuple_fields(self) -> <DbInterner as rustc_type_ir::Interner>::Tys {
        todo!()
    }

    fn to_opt_closure_kind(self) -> Option<rustc_type_ir::ClosureKind> {
        todo!()
    }

    fn from_closure_kind(interner: DbInterner, kind: rustc_type_ir::ClosureKind) -> Self {
        todo!()
    }

    fn from_coroutine_closure_kind(interner: DbInterner, kind: rustc_type_ir::ClosureKind) -> Self {
        todo!()
    }

    fn discriminant_ty(self, interner: DbInterner) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        todo!()
    }

    fn async_destructor_ty(
        self,
        interner: DbInterner,
    ) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        todo!()
    }
}

impl rustc_type_ir::inherent::Tys<DbInterner> for Tys {
    fn inputs(self) -> <DbInterner as rustc_type_ir::Interner>::FnInputTys {
        todo!()
    }

    fn output(self) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        todo!()
    }
}

impl ParamLike for ParamTy {
    fn index(self) -> u32 {
        self.index
    }
}

impl BoundVarLike<DbInterner> for BoundTy {
    fn var(self) -> rustc_type_ir::BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        todo!()
    }
}

impl PlaceholderLike for PlaceholderType {
    fn universe(self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(self) -> rustc_type_ir::BoundVar {
        self.bound.var
    }

    fn with_updated_universe(self, ui: rustc_type_ir::UniverseIndex) -> Self {
        todo!()
    }

    fn new(ui: rustc_type_ir::UniverseIndex, var: rustc_type_ir::BoundVar) -> Self {
        todo!()
    }
}
