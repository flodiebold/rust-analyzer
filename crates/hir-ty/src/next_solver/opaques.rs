use std::ops::Deref;

use intern::Interned;
use rustc_type_ir::{
    fold::TypeFoldable,
    solve::{ExternalConstraintsData, PredefinedOpaquesData},
    visit::TypeVisitable,
};

use super::{DbInterner, DefId};

pub type OpaqueTypeKey = rustc_type_ir::OpaqueTypeKey<DbInterner>;

// TODO doesn't work to intern these, because they need to implement Deref
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PredefinedOpaques(&'static PredefinedOpaquesData<DbInterner>);
interned_struct!(ExternalConstraints, ExternalConstraintsData<DbInterner>);

interned_vec!(DefiningOpaqueTypes, DefId);

impl DbInterner {
    pub(super) fn mk_predefined_opaques_in_body(
        self,
        data: PredefinedOpaquesData<Self>,
    ) -> PredefinedOpaques {
        PredefinedOpaques(Box::leak(Box::new(data)))
    }

    pub(super) fn mk_external_constraints(
        self,
        data: ExternalConstraintsData<Self>,
    ) -> ExternalConstraints {
        self.with_db(|db| db.intern_rustc_external_constraints(InternedExternalConstraints(data)))
    }
}

impl Deref for PredefinedOpaques {
    type Target = PredefinedOpaquesData<DbInterner>;

    fn deref(&self) -> &Self::Target {
        &self.0
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
