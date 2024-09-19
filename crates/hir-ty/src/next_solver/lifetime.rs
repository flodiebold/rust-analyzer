use rustc_type_ir::{
    fold::TypeFoldable,
    inherent::{IntoKind, PlaceholderLike},
    relate::Relate,
    visit::{Flags, TypeVisitable},
    RegionKind,
};

use super::{DbInterner, PlaceholderRegion, Region};

impl IntoKind for Region {
    type Kind = RegionKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        self.kind
    }
}

impl TypeVisitable<DbInterner> for Region {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for Region {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl Relate<DbInterner> for Region {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        todo!()
    }
}

impl Flags for Region {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        todo!()
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        todo!()
    }
}

impl rustc_type_ir::inherent::Region<DbInterner> for Region {
    fn new_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: <DbInterner as rustc_type_ir::Interner>::BoundRegion,
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

    fn new_static(interner: DbInterner) -> Self {
        todo!()
    }
}

impl PlaceholderLike for PlaceholderRegion {
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
