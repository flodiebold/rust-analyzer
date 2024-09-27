use std::ops::Deref;

use rustc_type_ir::{
    fold::TypeFoldable,
    solve::{ExternalConstraintsData, PredefinedOpaquesData},
    visit::TypeVisitable,
};

use super::{DbInterner, DefId};

pub type OpaqueTypeKey = rustc_type_ir::OpaqueTypeKey<DbInterner>;

// TODO doesn't work to intern these, because they need to implement Deref
interned_struct!(PredefinedOpaques, PredefinedOpaquesData<DbInterner>);
interned_struct!(ExternalConstraints, ExternalConstraintsData<DbInterner>);

interned_vec!(DefiningOpaqueTypes, DefId);

impl DbInterner {
    pub(super) fn mk_predefined_opaques_in_body(
        self,
        data: PredefinedOpaquesData<Self>,
    ) -> PredefinedOpaques {
        self.with_db(|db| db.intern_rustc_predefined_opaques(InternedPredefinedOpaques(data)))
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
