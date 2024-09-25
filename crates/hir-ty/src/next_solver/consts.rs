use rustc_type_ir::{
    fold::{TypeFoldable, TypeSuperFoldable},
    inherent::{IntoKind, PlaceholderLike},
    relate::Relate,
    visit::{Flags, TypeSuperVisitable, TypeVisitable},
    ConstKind,
};

use super::{DbInterner, Placeholder, Symbol};

interned_struct!(Const, rustc_type_ir::ConstKind<DbInterner>);

pub type PlaceholderConst = Placeholder<BoundConst>;

#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)] // FIXME implement manually
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

// TODO define these
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct ValueConst;
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct ExprConst;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] // FIXME implement Debug by hand
pub struct BoundConst {
    pub var: rustc_type_ir::BoundVar,
}

impl rustc_type_ir::inherent::ParamLike for ParamConst {
    fn index(self) -> u32 {
        self.index
    }
}

impl IntoKind for Const {
    type Kind = ConstKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        todo!()
    }
}

impl TypeVisitable<DbInterner> for Const {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeSuperVisitable<DbInterner> for Const {
    fn super_visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for Const {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl TypeSuperFoldable<DbInterner> for Const {
    fn try_super_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl Relate<DbInterner> for Const {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        todo!()
    }
}

impl Flags for Const {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        todo!()
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        todo!()
    }
}

impl rustc_type_ir::inherent::Const<DbInterner> for Const {
    fn try_to_target_usize(self, interner: DbInterner) -> Option<u64> {
        todo!()
    }

    fn new_infer(interner: DbInterner, var: rustc_type_ir::InferConst) -> Self {
        todo!()
    }

    fn new_var(interner: DbInterner, var: rustc_type_ir::ConstVid) -> Self {
        todo!()
    }

    fn new_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: <DbInterner as rustc_type_ir::Interner>::BoundConst,
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

    fn new_unevaluated(
        interner: DbInterner,
        uv: rustc_type_ir::UnevaluatedConst<DbInterner>,
    ) -> Self {
        todo!()
    }

    fn new_expr(
        interner: DbInterner,
        expr: <DbInterner as rustc_type_ir::Interner>::ExprConst,
    ) -> Self {
        todo!()
    }

    fn new_error(
        interner: DbInterner,
        guar: <DbInterner as rustc_type_ir::Interner>::ErrorGuaranteed,
    ) -> Self {
        todo!()
    }
}

impl PlaceholderLike for PlaceholderConst {
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

impl TypeVisitable<DbInterner> for ExprConst {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for ExprConst {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl Relate<DbInterner> for ExprConst {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        todo!()
    }
}

impl rustc_type_ir::inherent::ExprConst<DbInterner> for ExprConst {
    fn args(self) -> <DbInterner as rustc_type_ir::Interner>::GenericArgs {
        todo!()
    }
}
