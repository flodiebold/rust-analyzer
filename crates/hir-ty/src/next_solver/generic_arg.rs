use rustc_type_ir::{
    fold::TypeFoldable, inherent::IntoKind, relate::Relate, visit::TypeVisitable, GenericArgKind,
    TermKind,
};

use super::{Const, DbInterner, DefId, Region, Ty};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(Ty),
    Lifetime(Region),
    Const(Const),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Term {
    Ty(Ty),
    Const(Const),
}

interned_vec!(GenericArgs, GenericArg, slice);

impl From<Ty> for GenericArg {
    fn from(value: Ty) -> Self {
        Self::Ty(value)
    }
}

impl From<Region> for GenericArg {
    fn from(value: Region) -> Self {
        Self::Lifetime(value)
    }
}

impl From<Const> for GenericArg {
    fn from(value: Const) -> Self {
        Self::Const(value)
    }
}

impl IntoKind for GenericArg {
    type Kind = GenericArgKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        match self {
            GenericArg::Ty(ty) => GenericArgKind::Type(ty),
            GenericArg::Lifetime(region) => GenericArgKind::Lifetime(region),
            GenericArg::Const(c) => GenericArgKind::Const(c),
        }
    }
}

impl TypeVisitable<DbInterner> for GenericArg {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        match self {
            GenericArg::Lifetime(lt) => lt.visit_with(visitor),
            GenericArg::Ty(ty) => ty.visit_with(visitor),
            GenericArg::Const(ct) => ct.visit_with(visitor),
        }
    }
}

impl TypeFoldable<DbInterner> for GenericArg {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        match self.kind() {
            GenericArgKind::Lifetime(lt) => lt.try_fold_with(folder).map(Into::into),
            GenericArgKind::Type(ty) => ty.try_fold_with(folder).map(Into::into),
            GenericArgKind::Const(ct) => ct.try_fold_with(folder).map(Into::into),
        }
    }
}

impl Relate<DbInterner> for GenericArg {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        match (a.kind(), b.kind()) {
            (GenericArgKind::Lifetime(a_lt), GenericArgKind::Lifetime(b_lt)) => {
                Ok(relation.relate(a_lt, b_lt)?.into())
            }
            (GenericArgKind::Type(a_ty), GenericArgKind::Type(b_ty)) => {
                Ok(relation.relate(a_ty, b_ty)?.into())
            }
            (GenericArgKind::Const(a_ct), GenericArgKind::Const(b_ct)) => {
                Ok(relation.relate(a_ct, b_ct)?.into())
            }
            (GenericArgKind::Lifetime(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
            (GenericArgKind::Type(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
            (GenericArgKind::Const(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
        }
    }
}

impl rustc_type_ir::inherent::GenericArg<DbInterner> for GenericArg {}

impl rustc_type_ir::inherent::GenericArgs<DbInterner> for GenericArgs {
    fn rebase_onto(
        self,
        interner: DbInterner,
        source_def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        target: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> <DbInterner as rustc_type_ir::Interner>::GenericArgs {
        todo!()
    }

    fn type_at(self, i: usize) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        todo!()
    }

    fn region_at(self, i: usize) -> <DbInterner as rustc_type_ir::Interner>::Region {
        todo!()
    }

    fn const_at(self, i: usize) -> <DbInterner as rustc_type_ir::Interner>::Const {
        todo!()
    }

    fn identity_for_item(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
    ) -> <DbInterner as rustc_type_ir::Interner>::GenericArgs {
        todo!()
    }

    fn extend_with_error(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        original_args: &[<DbInterner as rustc_type_ir::Interner>::GenericArg],
    ) -> <DbInterner as rustc_type_ir::Interner>::GenericArgs {
        todo!()
    }

    fn split_closure_args(self) -> rustc_type_ir::ClosureArgsParts<DbInterner> {
        todo!()
    }

    fn split_coroutine_closure_args(self) -> rustc_type_ir::CoroutineClosureArgsParts<DbInterner> {
        todo!()
    }

    fn split_coroutine_args(self) -> rustc_type_ir::CoroutineArgsParts<DbInterner> {
        todo!()
    }
}

impl IntoKind for Term {
    type Kind = TermKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        match self {
            Term::Ty(ty) => TermKind::Ty(ty),
            Term::Const(c) => TermKind::Const(c),
        }
    }
}

impl From<Ty> for Term {
    fn from(value: Ty) -> Self {
        Self::Ty(value)
    }
}

impl From<Const> for Term {
    fn from(value: Const) -> Self {
        Self::Const(value)
    }
}

impl TypeVisitable<DbInterner> for Term {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        match self {
            Term::Ty(ty) => ty.visit_with(visitor),
            Term::Const(ct) => ct.visit_with(visitor),
        }
    }
}

impl TypeFoldable<DbInterner> for Term {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        match self.kind() {
            TermKind::Ty(ty) => ty.try_fold_with(folder).map(Into::into),
            TermKind::Const(ct) => ct.try_fold_with(folder).map(Into::into),
        }
    }
}

impl Relate<DbInterner> for Term {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        match (a.kind(), b.kind()) {
            (TermKind::Ty(a_ty), TermKind::Ty(b_ty)) => Ok(relation.relate(a_ty, b_ty)?.into()),
            (TermKind::Const(a_ct), TermKind::Const(b_ct)) => {
                Ok(relation.relate(a_ct, b_ct)?.into())
            }
            (TermKind::Ty(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
            (TermKind::Const(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
        }
    }
}

impl rustc_type_ir::inherent::Term<DbInterner> for Term {}

impl DbInterner {
    pub(super) fn mk_args(self, args: &[GenericArg]) -> GenericArgs {
        todo!()
    }

    pub(super) fn mk_args_from_iter<I, T>(self, args: I) -> T::Output
    where
        I: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<GenericArg, GenericArgs>,
    {
        todo!()
    }

    pub(super) fn check_args_compatible(self, def_id: DefId, args: GenericArgs) -> bool {
        // TODO
        true
    }

    pub(super) fn debug_assert_args_compatible(self, def_id: DefId, args: GenericArgs) {
        // TODO
    }
}
