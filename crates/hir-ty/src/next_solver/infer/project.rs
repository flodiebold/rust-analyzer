//! Code for projecting associated types out of trait references.

use ena::undo_log::Rollback;
use tracing::{debug, info};

use crate::next_solver::{AliasTerm, ParamEnv, Term, infer::snapshot::undo_log::InferCtxtUndoLogs};

use self::snapshot_map::{SnapshotMapRef, SnapshotMapStorage};

use super::{
    data_structures::snapshot_map, select::EvaluationResult, traits::PredicateObligations,
};

pub(crate) type ProjectUndoLog<'db> =
    snapshot_map::UndoLog<ProjectionCacheKey<'db>, ProjectionCacheEntry<'db>>;

#[derive(Clone)]
pub struct MismatchedProjectionTypes {
    pub err: (),
    //pub err: error::TypeError,
}

#[derive(Clone, Debug)]
pub struct Normalized<'db, T> {
    pub value: T,
    pub obligations: PredicateObligations<'db>,
}

pub type NormalizedTerm<'db> = Normalized<'db, Term<'db>>;

impl<'db, T> Normalized<'db, T> {
    pub fn with<U>(self, value: U) -> Normalized<'db, U> {
        Normalized { value, obligations: self.obligations }
    }
}

// # Cache

/// The projection cache. Unlike the standard caches, this can include
/// infcx-dependent type variables, therefore we have to roll the
/// cache back each time we roll a snapshot back, to avoid assumptions
/// on yet-unresolved inference variables. Types with placeholder
/// regions also have to be removed when the respective snapshot ends.
///
/// Because of that, projection cache entries can be "stranded" and left
/// inaccessible when type variables inside the key are resolved. We make no
/// attempt to recover or remove "stranded" entries, but rather let them be
/// (for the lifetime of the infcx).
///
/// Entries in the projection cache might contain inference variables
/// that will be resolved by obligations on the projection cache entry (e.g.,
/// when a type parameter in the associated type is constrained through
/// an "RFC 447" projection on the impl).
///
/// When working with a fulfillment context, the derived obligations of each
/// projection cache entry will be registered on the fulfillcx, so any users
/// that can wait for a fulfillcx fixed point need not care about this. However,
/// users that don't wait for a fixed point (e.g., trait evaluation) have to
/// resolve the obligations themselves to make sure the projected result is
/// ok and avoid issues like #43132.
///
/// If that is done, after evaluation the obligations, it is a good idea to
/// call `ProjectionCache::complete` to make sure the obligations won't be
/// re-evaluated and avoid an exponential worst-case.
//
// FIXME: we probably also want some sort of cross-infcx cache here to
// reduce the amount of duplication. Let's see what we get with the Chalk reforms.
pub struct ProjectionCache<'a, 'db> {
    map: &'a mut SnapshotMapStorage<ProjectionCacheKey<'db>, ProjectionCacheEntry<'db>>,
    undo_log: &'a mut InferCtxtUndoLogs<'db>,
}

#[derive(Clone, Default)]
pub struct ProjectionCacheStorage<'db> {
    map: SnapshotMapStorage<ProjectionCacheKey<'db>, ProjectionCacheEntry<'db>>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ProjectionCacheKey<'db> {
    term: AliasTerm<'db>,
    param_env: ParamEnv<'db>,
}

impl<'db> ProjectionCacheKey<'db> {
    pub fn new(term: AliasTerm<'db>, param_env: ParamEnv<'db>) -> Self {
        Self { term, param_env }
    }
}

#[derive(Clone, Debug)]
pub enum ProjectionCacheEntry<'db> {
    InProgress,
    Ambiguous,
    Recur,
    Error,
    NormalizedTerm {
        ty: NormalizedTerm<'db>,
        /// If we were able to successfully evaluate the corresponding cache
        /// entry key during predicate evaluation, then this field stores the
        /// final result obtained from evaluating all of the projection
        /// sub-obligations. During evaluation, we will skip evaluating the
        /// cached sub-obligations in `ty` if this field is set. Evaluation
        /// only cares about the final result, so we don't care about any
        /// region constraint side-effects produced by evaluating the
        /// sub-obligations.
        ///
        /// Additionally, we will clear out the sub-obligations entirely if we
        /// ever evaluate the cache entry (along with all its sub obligations)
        /// to `EvaluatedToOk`. This affects all users of the cache, not just
        /// evaluation. Since a result of `EvaluatedToOk` means that there were
        /// no region obligations that need to be tracked, it's fine to forget
        /// about the sub-obligations - they don't provide any additional
        /// information. However, we do *not* discard any obligations when we
        /// see `EvaluatedToOkModuloRegions` - we don't know which
        /// sub-obligations may introduce region constraints, so we keep them
        /// all to be safe.
        ///
        /// When we are not performing evaluation (e.g. in
        /// `FulfillmentContext`), we ignore this field, and always re-process
        /// the cached sub-obligations (which may have been cleared out - see
        /// the above paragraph). This ensures that we do not lose any regions
        /// constraints that arise from processing the sub-obligations.
        complete: Option<EvaluationResult>,
    },
}

impl<'db> ProjectionCacheStorage<'db> {
    #[inline]
    pub(crate) fn with_log<'a>(
        &'a mut self,
        undo_log: &'a mut InferCtxtUndoLogs<'db>,
    ) -> ProjectionCache<'a, 'db> {
        ProjectionCache { map: &mut self.map, undo_log }
    }
}

impl<'db> ProjectionCache<'_, 'db> {
    #[inline]
    fn map(
        &mut self,
    ) -> SnapshotMapRef<
        '_,
        ProjectionCacheKey<'db>,
        ProjectionCacheEntry<'db>,
        InferCtxtUndoLogs<'db>,
    > {
        self.map.with_log(self.undo_log)
    }

    pub fn clear(&mut self) {
        self.map().clear();
    }

    /// Try to start normalize `key`; returns an error if
    /// normalization already occurred (this error corresponds to a
    /// cache hit, so it's actually a good thing).
    pub fn try_start(
        &mut self,
        key: ProjectionCacheKey<'db>,
    ) -> Result<(), ProjectionCacheEntry<'db>> {
        let mut map = self.map();
        if let Some(entry) = map.get(&key) {
            return Err(entry.clone());
        }

        map.insert(key, ProjectionCacheEntry::InProgress);
        Ok(())
    }

    /// Indicates that `key` was normalized to `value`.
    pub fn insert_term(&mut self, key: ProjectionCacheKey<'db>, value: NormalizedTerm<'db>) {
        debug!(
            "ProjectionCacheEntry::insert_ty: adding cache entry: key={:?}, value={:?}",
            key, value
        );
        let mut map = self.map();
        if let Some(ProjectionCacheEntry::Recur) = map.get(&key) {
            debug!("Not overwriting Recur");
            return;
        }
        let fresh_key = map.insert(
            key.clone(),
            ProjectionCacheEntry::NormalizedTerm { ty: value, complete: None },
        );
        assert!(!fresh_key, "never started projecting `{key:?}`");
    }

    /// Mark the relevant projection cache key as having its derived obligations
    /// complete, so they won't have to be re-computed (this is OK to do in a
    /// snapshot - if the snapshot is rolled back, the obligations will be
    /// marked as incomplete again).
    pub fn complete(&mut self, key: ProjectionCacheKey<'db>, result: EvaluationResult) {
        let mut map = self.map();
        match map.get(&key) {
            Some(ProjectionCacheEntry::NormalizedTerm { ty, complete: _ }) => {
                info!("ProjectionCacheEntry::complete({:?}) - completing {:?}", key, ty);
                let mut ty = ty.clone();
                if result.must_apply_considering_regions() {
                    ty.obligations = PredicateObligations::new();
                }
                map.insert(
                    key,
                    ProjectionCacheEntry::NormalizedTerm { ty, complete: Some(result) },
                );
            }
            ref value => {
                // Type inference could "strand behind" old cache entries. Leave
                // them alone for now.
                info!("ProjectionCacheEntry::complete({:?}) - ignoring {:?}", key, value);
            }
        };
    }

    pub fn is_complete(&mut self, key: ProjectionCacheKey<'db>) -> Option<EvaluationResult> {
        self.map().get(&key).and_then(|res| match res {
            ProjectionCacheEntry::NormalizedTerm { ty: _, complete } => *complete,
            _ => None,
        })
    }

    /// Indicates that trying to normalize `key` resulted in
    /// ambiguity. No point in trying it again then until we gain more
    /// type information (in which case, the "fully resolved" key will
    /// be different).
    pub fn ambiguous(&mut self, key: ProjectionCacheKey<'db>) {
        let fresh = self.map().insert(key.clone(), ProjectionCacheEntry::Ambiguous);
        assert!(!fresh, "never started projecting `{key:?}`");
    }

    /// Indicates that while trying to normalize `key`, `key` was required to
    /// be normalized again. Selection or evaluation should eventually report
    /// an error here.
    pub fn recur(&mut self, key: ProjectionCacheKey<'db>) {
        let fresh = self.map().insert(key.clone(), ProjectionCacheEntry::Recur);
        assert!(!fresh, "never started projecting `{key:?}`");
    }

    /// Indicates that trying to normalize `key` resulted in
    /// error.
    pub fn error(&mut self, key: ProjectionCacheKey<'db>) {
        let fresh = self.map().insert(key.clone(), ProjectionCacheEntry::Error);
        assert!(!fresh, "never started projecting `{key:?}`");
    }
}

impl<'db> Rollback<ProjectUndoLog<'db>> for ProjectionCacheStorage<'db> {
    fn reverse(&mut self, undo: ProjectUndoLog<'db>) {
        self.map.reverse(undo);
    }
}
