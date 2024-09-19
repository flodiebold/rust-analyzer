use std::ops::Deref;

use rustc_type_ir::{
    fold::TypeFoldable,
    solve::{ExternalConstraintsData, PredefinedOpaquesData},
    visit::TypeVisitable,
};

use super::{DbInterner, ExternalConstraints, PredefinedOpaques};

impl Deref for PredefinedOpaques {
    type Target = PredefinedOpaquesData<DbInterner>;

    fn deref(&self) -> &Self::Target {
        todo!()
    }
}

impl TypeVisitable<DbInterner> for PredefinedOpaques {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for PredefinedOpaques {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl Deref for ExternalConstraints {
    type Target = ExternalConstraintsData<DbInterner>;

    fn deref(&self) -> &Self::Target {
        todo!()
    }
}

impl TypeVisitable<DbInterner> for ExternalConstraints {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for ExternalConstraints {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}
