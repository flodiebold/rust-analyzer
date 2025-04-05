use std::ops::Range;

use ena::snapshot_vec as sv;
use ena::unify as ut;
use rustc_type_ir::ConstVid;
use rustc_type_ir::FloatVid;
use rustc_type_ir::InferConst;
use rustc_type_ir::IntVid;
use rustc_type_ir::RegionKind;
use rustc_type_ir::RegionVid;
use rustc_type_ir::TyVid;
use rustc_type_ir::TypeFoldable;
use rustc_type_ir::TypeFolder;
use rustc_type_ir::TypeSuperFoldable;
use rustc_type_ir::TypeVisitableExt;
use rustc_type_ir::inherent::IntoKind;
use rustc_type_ir::inherent::Span as _;
use tracing::instrument;
use ut::UnifyKey;

use super::VariableLengths;
use crate::next_solver::ConstKind;
use crate::next_solver::infer::type_variable::TypeVariableOrigin;
use crate::next_solver::infer::unify_key::ConstVariableValue;
use crate::next_solver::infer::unify_key::ConstVidKey;
use crate::next_solver::infer::{ConstVariableOrigin, RegionVariableOrigin, UnificationTable};

use crate::next_solver::{
    AliasTy, Binder, Const, DbInterner, DbIr, Goal, ParamEnv, Predicate, PredicateKind, Region,
    Span, Ty, TyKind,
    infer::{
        DefineOpaqueTypes, InferCtxt, SubregionOrigin, TypeTrace,
        traits::{Obligation, PredicateObligations},
    },
};
use rustc_type_ir::{
    AliasRelationDirection, AliasTyKind, InferTy, Upcast, Variance,
    relate::{
        Relate, TypeRelation, VarianceDiagInfo,
        combine::{super_combine_consts, super_combine_tys},
    },
};

fn vars_since_snapshot<'db, T>(
    table: &UnificationTable<'_, 'db, T>,
    snapshot_var_len: usize,
) -> Range<T>
where
    T: UnifyKey,
    super::UndoLog<'db>: From<sv::UndoLog<ut::Delegate<T>>>,
{
    T::from_index(snapshot_var_len as u32)..T::from_index(table.len() as u32)
}

fn const_vars_since_snapshot<'db>(
    table: &mut UnificationTable<'_, 'db, ConstVidKey<'db>>,
    snapshot_var_len: usize,
) -> (Range<ConstVid>, Vec<ConstVariableOrigin>) {
    let range = vars_since_snapshot(table, snapshot_var_len);

    (
        range.start.vid..range.end.vid,
        (range.start.index()..range.end.index())
            .map(|index| match table.probe_value(ConstVid::from_u32(index)) {
                ConstVariableValue::Known { value: _ } => {
                    ConstVariableOrigin { param_def_id: None, span: Span::dummy() }
                }
                ConstVariableValue::Unknown { origin, universe: _ } => origin,
            })
            .collect(),
    )
}

impl<'db> InferCtxt<'db> {
    /// This rather funky routine is used while processing expected
    /// types. What happens here is that we want to propagate a
    /// coercion through the return type of a fn to its
    /// argument. Consider the type of `Option::Some`, which is
    /// basically `for<T> fn(T) -> Option<T>`. So if we have an
    /// expression `Some(&[1, 2, 3])`, and that has the expected type
    /// `Option<&[u32]>`, we would like to type check `&[1, 2, 3]`
    /// with the expectation of `&[u32]`. This will cause us to coerce
    /// from `&[u32; 3]` to `&[u32]` and make the users life more
    /// pleasant.
    ///
    /// The way we do this is using `fudge_inference_if_ok`. What the
    /// routine actually does is to start a snapshot and execute the
    /// closure `f`. In our example above, what this closure will do
    /// is to unify the expectation (`Option<&[u32]>`) with the actual
    /// return type (`Option<?T>`, where `?T` represents the variable
    /// instantiated for `T`). This will cause `?T` to be unified
    /// with `&?a [u32]`, where `?a` is a fresh lifetime variable. The
    /// input type (`?T`) is then returned by `f()`.
    ///
    /// At this point, `fudge_inference_if_ok` will normalize all type
    /// variables, converting `?T` to `&?a [u32]` and end the
    /// snapshot. The problem is that we can't just return this type
    /// out, because it references the region variable `?a`, and that
    /// region variable was popped when we popped the snapshot.
    ///
    /// So what we do is to keep a list (`region_vars`, in the code below)
    /// of region variables created during the snapshot (here, `?a`). We
    /// fold the return value and replace any such regions with a *new*
    /// region variable (e.g., `?b`) and return the result (`&?b [u32]`).
    /// This can then be used as the expectation for the fn argument.
    ///
    /// The important point here is that, for soundness purposes, the
    /// regions in question are not particularly important. We will
    /// use the expected types to guide coercions, but we will still
    /// type-check the resulting types from those coercions against
    /// the actual types (`?T`, `Option<?T>`) -- and remember that
    /// after the snapshot is popped, the variable `?T` is no longer
    /// unified.
    #[instrument(skip(self, f), level = "debug")]
    pub fn fudge_inference_if_ok<T, E, F>(&self, f: F) -> Result<T, E>
    where
        F: FnOnce() -> Result<T, E>,
        T: TypeFoldable<DbInterner<'db>>,
    {
        let variable_lengths = self.variable_lengths();
        let (snapshot_vars, value) = self.probe(|_| {
            let value = f()?;
            // At this point, `value` could in principle refer
            // to inference variables that have been created during
            // the snapshot. Once we exit `probe()`, those are
            // going to be popped, so we will have to
            // eliminate any references to them.
            let snapshot_vars = SnapshotVarData::new(self, variable_lengths);
            Ok((snapshot_vars, self.resolve_vars_if_possible(value)))
        })?;

        // At this point, we need to replace any of the now-popped
        // type/region variables that appear in `value` with a fresh
        // variable of the appropriate kind. We can't do this during
        // the probe because they would just get popped then too. =)
        Ok(self.fudge_inference(snapshot_vars, value))
    }

    fn fudge_inference<T: TypeFoldable<DbInterner<'db>>>(
        &self,
        snapshot_vars: SnapshotVarData,
        value: T,
    ) -> T {
        // Micro-optimization: if no variables have been created, then
        // `value` can't refer to any of them. =) So we can just return it.
        if snapshot_vars.is_empty() {
            value
        } else {
            value.fold_with(&mut InferenceFudger { infcx: self, snapshot_vars })
        }
    }
}

struct SnapshotVarData {
    region_vars: (Range<RegionVid>, Vec<RegionVariableOrigin>),
    type_vars: (Range<TyVid>, Vec<TypeVariableOrigin>),
    int_vars: Range<IntVid>,
    float_vars: Range<FloatVid>,
    const_vars: (Range<ConstVid>, Vec<ConstVariableOrigin>),
}

impl SnapshotVarData {
    fn new(infcx: &InferCtxt<'_>, vars_pre_snapshot: VariableLengths) -> SnapshotVarData {
        let mut inner = infcx.inner.borrow_mut();
        let region_vars = inner
            .unwrap_region_constraints()
            .vars_since_snapshot(vars_pre_snapshot.region_constraints_len);
        let type_vars = inner.type_variables().vars_since_snapshot(vars_pre_snapshot.type_var_len);
        let int_vars =
            vars_since_snapshot(&inner.int_unification_table(), vars_pre_snapshot.int_var_len);
        let float_vars =
            vars_since_snapshot(&inner.float_unification_table(), vars_pre_snapshot.float_var_len);

        let const_vars = const_vars_since_snapshot(
            &mut inner.const_unification_table(),
            vars_pre_snapshot.const_var_len,
        );
        SnapshotVarData { region_vars, type_vars, int_vars, float_vars, const_vars }
    }

    fn is_empty(&self) -> bool {
        let SnapshotVarData { region_vars, type_vars, int_vars, float_vars, const_vars } = self;
        region_vars.0.is_empty()
            && type_vars.0.is_empty()
            && int_vars.is_empty()
            && float_vars.is_empty()
            && const_vars.0.is_empty()
    }
}

struct InferenceFudger<'a, 'db> {
    infcx: &'a InferCtxt<'db>,
    snapshot_vars: SnapshotVarData,
}

impl<'a, 'db> TypeFolder<DbInterner<'db>> for InferenceFudger<'a, 'db> {
    fn cx(&self) -> DbInterner<'db> {
        self.infcx.interner
    }

    fn fold_ty(&mut self, ty: Ty<'db>) -> Ty<'db> {
        if let TyKind::Infer(infer_ty) = ty.clone().kind() {
            match infer_ty {
                InferTy::TyVar(vid) => {
                    if self.snapshot_vars.type_vars.0.contains(&vid) {
                        // This variable was created during the fudging.
                        // Recreate it with a fresh variable here.
                        let idx = vid.as_usize() - self.snapshot_vars.type_vars.0.start.as_usize();
                        let origin = self.snapshot_vars.type_vars.1[idx];
                        self.infcx.next_ty_var_with_origin(origin)
                    } else {
                        // This variable was created before the
                        // "fudging". Since we refresh all type
                        // variables to their binding anyhow, we know
                        // that it is unbound, so we can just return
                        // it.
                        debug_assert!(
                            self.infcx.inner.borrow_mut().type_variables().probe(vid).is_unknown()
                        );
                        ty
                    }
                }
                InferTy::IntVar(vid) => {
                    if self.snapshot_vars.int_vars.contains(&vid) {
                        self.infcx.next_int_var()
                    } else {
                        ty
                    }
                }
                InferTy::FloatVar(vid) => {
                    if self.snapshot_vars.float_vars.contains(&vid) {
                        self.infcx.next_float_var()
                    } else {
                        ty
                    }
                }
                InferTy::FreshTy(_) | InferTy::FreshIntTy(_) | InferTy::FreshFloatTy(_) => {
                    unreachable!("unexpected fresh infcx var")
                }
            }
        } else if ty.has_infer() {
            ty.super_fold_with(self)
        } else {
            ty
        }
    }

    fn fold_region(&mut self, r: Region<'db>) -> Region<'db> {
        if let RegionKind::ReVar(vid) = r.clone().kind() {
            if self.snapshot_vars.region_vars.0.contains(&vid) {
                let idx = vid.index() - self.snapshot_vars.region_vars.0.start.index();
                let origin = self.snapshot_vars.region_vars.1[idx].clone();
                self.infcx.next_region_var(origin)
            } else {
                r
            }
        } else {
            r
        }
    }

    fn fold_const(&mut self, ct: Const<'db>) -> Const<'db> {
        if let ConstKind::Infer(infer_ct) = ct.clone().kind() {
            match infer_ct {
                InferConst::Var(vid) => {
                    if self.snapshot_vars.const_vars.0.contains(&vid) {
                        let idx = vid.index() - self.snapshot_vars.const_vars.0.start.index();
                        let origin = self.snapshot_vars.const_vars.1[idx];
                        self.infcx.next_const_var_with_origin(origin)
                    } else {
                        ct
                    }
                }
                InferConst::Fresh(_) => {
                    unreachable!("unexpected fresh infcx var")
                }
            }
        } else if ct.has_infer() {
            ct.super_fold_with(self)
        } else {
            ct
        }
    }
}
