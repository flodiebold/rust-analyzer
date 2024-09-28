use rustc_type_ir::{
    fold::{TypeFoldable, TypeSuperFoldable},
    inherent::{BoundVarLike, IntoKind, ParamLike, PlaceholderLike},
    relate::Relate,
    visit::{Flags, TypeSuperVisitable, TypeVisitable},
    BoundVar, TyKind,
};

use super::{
    with_db_out_of_thin_air, BoundVarKind, DbInterner, DefId, GenericArgs, Placeholder, Symbol,
};

pub type FnHeader = rustc_type_ir::FnHeader<DbInterner>;

interned_struct!(Ty, TyKind<DbInterner>);
interned_vec!(Tys, Ty, slice);

pub type PlaceholderTy = Placeholder<BoundTy>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)] // FIXME implement Debug by hand
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] // FIXME implement Debug by hand
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BoundTyKind {
    Anon,
    Param(DefId, Symbol),
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ErrorGuaranteed;

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

impl DbInterner {
    fn mk_ty(self, kind: rustc_type_ir::TyKind<DbInterner>) -> Ty {
        self.with_db(|db| db.intern_rustc_ty(InternedTy(kind)))
    }

    fn mk_tys(self, tys: &[Ty]) -> Tys {
        self.with_db(|db| db.intern_rustc_tys(InternedTys(tys.to_vec())))
    }
    fn mk_tys_from_iter(self, tys: impl Iterator<Item = Ty>) -> Tys {
        self.with_db(|db| db.intern_rustc_tys(InternedTys(tys.collect())))
    }
}

impl rustc_type_ir::inherent::Ty<DbInterner> for Ty {
    // FIXME: these could be stored directly for performance like rustc does
    fn new_unit(interner: DbInterner) -> Self {
        interner.mk_ty(TyKind::Tuple(Default::default()))
    }

    fn new_bool(interner: DbInterner) -> Self {
        interner.mk_ty(TyKind::Bool)
    }

    fn new_u8(interner: DbInterner) -> Self {
        interner.mk_ty(TyKind::Uint(rustc_type_ir::UintTy::U8))
    }

    fn new_usize(interner: DbInterner) -> Self {
        interner.mk_ty(TyKind::Uint(rustc_type_ir::UintTy::Usize))
    }

    fn new_infer(interner: DbInterner, var: rustc_type_ir::InferTy) -> Self {
        interner.mk_ty(TyKind::Infer(var))
    }

    fn new_var(interner: DbInterner, var: rustc_type_ir::TyVid) -> Self {
        interner.mk_ty(TyKind::Infer(rustc_type_ir::InferTy::TyVar(var)))
    }

    fn new_param(interner: DbInterner, param: ParamTy) -> Self {
        interner.mk_ty(TyKind::Param(param))
    }

    fn new_placeholder(interner: DbInterner, param: PlaceholderTy) -> Self {
        interner.mk_ty(TyKind::Placeholder(param))
    }

    fn new_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: BoundTy,
    ) -> Self {
        interner.mk_ty(TyKind::Bound(debruijn, var))
    }

    fn new_anon_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: BoundVar,
    ) -> Self {
        interner.mk_ty(TyKind::Bound(debruijn, BoundTy { var, kind: BoundTyKind::Anon }))
    }

    fn new_alias(
        interner: DbInterner,
        kind: rustc_type_ir::AliasTyKind,
        alias_ty: rustc_type_ir::AliasTy<DbInterner>,
    ) -> Self {
        interner.mk_ty(TyKind::Alias(kind, alias_ty))
    }

    fn new_error(interner: DbInterner, guar: ErrorGuaranteed) -> Self {
        interner.mk_ty(TyKind::Error(guar))
    }

    fn new_adt(
        interner: DbInterner,
        adt_def: <DbInterner as rustc_type_ir::Interner>::AdtDef,
        args: GenericArgs,
    ) -> Self {
        interner.mk_ty(TyKind::Adt(adt_def, args))
    }

    fn new_foreign(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
    ) -> Self {
        interner.mk_ty(TyKind::Foreign(def_id))
    }

    fn new_dynamic(
        interner: DbInterner,
        preds: <DbInterner as rustc_type_ir::Interner>::BoundExistentialPredicates,
        region: <DbInterner as rustc_type_ir::Interner>::Region,
        kind: rustc_type_ir::DynKind,
    ) -> Self {
        interner.mk_ty(TyKind::Dynamic(preds, region, kind))
    }

    fn new_coroutine(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        interner.mk_ty(TyKind::Coroutine(def_id, args))
    }

    fn new_coroutine_closure(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        interner.mk_ty(TyKind::CoroutineClosure(def_id, args))
    }

    fn new_closure(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        interner.mk_ty(TyKind::Closure(def_id, args))
    }

    fn new_coroutine_witness(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        interner.mk_ty(TyKind::CoroutineWitness(def_id, args))
    }

    fn new_ptr(interner: DbInterner, ty: Self, mutbl: rustc_ast_ir::Mutability) -> Self {
        interner.mk_ty(TyKind::RawPtr(ty, mutbl))
    }

    fn new_ref(
        interner: DbInterner,
        region: <DbInterner as rustc_type_ir::Interner>::Region,
        ty: Self,
        mutbl: rustc_ast_ir::Mutability,
    ) -> Self {
        interner.mk_ty(TyKind::Ref(region, ty, mutbl))
    }

    fn new_array_with_const_len(
        interner: DbInterner,
        ty: Self,
        len: <DbInterner as rustc_type_ir::Interner>::Const,
    ) -> Self {
        interner.mk_ty(TyKind::Array(ty, len))
    }

    fn new_slice(interner: DbInterner, ty: Self) -> Self {
        interner.mk_ty(TyKind::Slice(ty))
    }

    fn new_tup(interner: DbInterner, tys: &[<DbInterner as rustc_type_ir::Interner>::Ty]) -> Self {
        interner.mk_ty(TyKind::Tuple(interner.mk_tys(tys)))
    }

    fn new_tup_from_iter<It, T>(interner: DbInterner, iter: It) -> T::Output
    where
        It: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<Self, Self>,
    {
        T::collect_and_apply(iter, |ts| Ty::new_tup(interner, ts))
    }

    fn new_fn_def(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        interner.mk_ty(TyKind::FnDef(def_id, args))
    }

    fn new_fn_ptr(
        interner: DbInterner,
        sig: rustc_type_ir::Binder<DbInterner, rustc_type_ir::FnSig<DbInterner>>,
    ) -> Self {
        let (sig_tys, header) = sig.split();
        interner.mk_ty(TyKind::FnPtr(sig_tys, header))
    }

    fn new_pat(
        interner: DbInterner,
        ty: Self,
        pat: <DbInterner as rustc_type_ir::Interner>::Pat,
    ) -> Self {
        interner.mk_ty(TyKind::Pat(ty, pat))
    }

    fn tuple_fields(self) -> <DbInterner as rustc_type_ir::Interner>::Tys {
        match self.kind() {
            TyKind::Tuple(args) => args,
            _ => panic!("tuple_fields called on non-tuple: {self:?}"),
        }
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
    fn var(self) -> BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        assert_eq!(self.kind, var.expect_ty())
    }
}

impl PlaceholderLike for PlaceholderTy {
    fn universe(self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(self) -> BoundVar {
        self.bound.var
    }

    fn with_updated_universe(self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, ..self }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, var: BoundVar) -> Self {
        Placeholder { universe: ui, bound: BoundTy { var, kind: BoundTyKind::Anon } }
    }
}
