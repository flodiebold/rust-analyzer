use ena::undo_log::UndoLogs;
use tracing::instrument;

use super::{OpaqueHiddenType, OpaqueTypeDecl, OpaqueTypeMap};
use crate::next_solver::{
    OpaqueTypeKey, Ty,
    infer::snapshot::undo_log::{InferCtxtUndoLogs, UndoLog},
};

#[derive(Default, Debug, Clone)]
pub(crate) struct OpaqueTypeStorage<'db> {
    /// Opaque types found in explicit return types and their
    /// associated fresh inference variable. Writeback resolves these
    /// variables to get the concrete type, which can be used to
    /// 'de-opaque' OpaqueTypeDecl, after typeck is done with all functions.
    pub opaque_types: OpaqueTypeMap<'db>,
}

impl<'db> OpaqueTypeStorage<'db> {
    #[instrument(level = "debug")]
    pub(crate) fn remove(&mut self, key: OpaqueTypeKey<'db>, idx: Option<OpaqueHiddenType<'db>>) {
        if let Some(idx) = idx {
            self.opaque_types.get_mut(&key).unwrap().hidden_type = idx;
        } else {
            // FIXME(#120456) - is `swap_remove` correct?
            match self.opaque_types.swap_remove(&key) {
                None => {
                    panic!("reverted opaque type inference that was never registered: {:?}", key)
                }
                Some(_) => {}
            }
        }
    }

    #[inline]
    pub(crate) fn with_log<'a>(
        &'a mut self,
        undo_log: &'a mut InferCtxtUndoLogs<'db>,
    ) -> OpaqueTypeTable<'db, 'a> {
        OpaqueTypeTable { storage: self, undo_log }
    }
}

impl<'db> Drop for OpaqueTypeStorage<'db> {
    fn drop(&mut self) {
        if !self.opaque_types.is_empty() {
            panic!("{:?}", self.opaque_types)
        }
    }
}

pub(crate) struct OpaqueTypeTable<'db, 'a> {
    storage: &'a mut OpaqueTypeStorage<'db>,

    undo_log: &'a mut InferCtxtUndoLogs<'db>,
}

impl<'db, 'a> OpaqueTypeTable<'db, 'a> {
    #[instrument(skip(self), level = "debug")]
    pub(crate) fn register(
        &mut self,
        key: OpaqueTypeKey<'db>,
        hidden_type: OpaqueHiddenType<'db>,
    ) -> Option<Ty<'db>> {
        if let Some(decl) = self.storage.opaque_types.get_mut(&key) {
            let prev = std::mem::replace(&mut decl.hidden_type, hidden_type);
            self.undo_log.push(UndoLog::OpaqueTypes(key, Some(prev.clone())));
            return Some(prev.ty);
        }
        let decl = OpaqueTypeDecl { hidden_type };
        self.storage.opaque_types.insert(key.clone(), decl);
        self.undo_log.push(UndoLog::OpaqueTypes(key, None));
        None
    }
}
