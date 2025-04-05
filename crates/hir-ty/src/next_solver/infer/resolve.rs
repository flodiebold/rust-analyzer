use rustc_type_ir::{
    ConstKind, FallibleTypeFolder, InferConst, InferTy, RegionKind, TyKind, TypeFoldable,
    TypeFolder, TypeSuperFoldable, TypeVisitableExt, data_structures::DelayedMap,
    inherent::IntoKind,
};

use crate::next_solver::{Const, DbInterner, Region, Ty};

use super::{FixupError, FixupResult, InferCtxt};

///////////////////////////////////////////////////////////////////////////
// OPPORTUNISTIC VAR RESOLVER

/// The opportunistic resolver can be used at any time. It simply replaces
/// type/const variables that have been unified with the things they have
/// been unified with (similar to `shallow_resolve`, but deep). This is
/// useful for printing messages etc but also required at various
/// points for correctness.
pub struct OpportunisticVarResolver<'a, 'db> {
    infcx: &'a InferCtxt<'db>,
    /// We're able to use a cache here as the folder does
    /// not have any mutable state.
    cache: DelayedMap<Ty<'db>, Ty<'db>>,
}

impl<'a, 'db> OpportunisticVarResolver<'a, 'db> {
    #[inline]
    pub fn new(infcx: &'a InferCtxt<'db>) -> Self {
        OpportunisticVarResolver { infcx, cache: Default::default() }
    }
}

impl<'a, 'db> TypeFolder<DbInterner<'db>> for OpportunisticVarResolver<'a, 'db> {
    fn cx(&self) -> DbInterner<'db> {
        self.infcx.interner
    }

    #[inline]
    fn fold_ty(&mut self, t: Ty<'db>) -> Ty<'db> {
        if !t.has_non_region_infer() {
            t // micro-optimize -- if there is nothing in this type that this fold affects...
        } else if let Some(ty) = self.cache.get(&t) {
            ty.clone()
        } else {
            let shallow = self.infcx.shallow_resolve(t.clone());
            let res = shallow.super_fold_with(self);
            assert!(self.cache.insert(t.clone(), res.clone()));
            res
        }
    }

    fn fold_const(&mut self, ct: Const<'db>) -> Const<'db> {
        if !ct.has_non_region_infer() {
            ct // micro-optimize -- if there is nothing in this const that this fold affects...
        } else {
            let ct = self.infcx.shallow_resolve_const(ct);
            ct.super_fold_with(self)
        }
    }
}

/// The opportunistic region resolver opportunistically resolves regions
/// variables to the variable with the least variable id. It is used when
/// normalizing projections to avoid hitting the recursion limit by creating
/// many versions of a predicate for types that in the end have to unify.
///
/// If you want to resolve type and const variables as well, call
/// [InferCtxt::resolve_vars_if_possible] first.
pub struct OpportunisticRegionResolver<'a, 'db> {
    infcx: &'a InferCtxt<'db>,
}

impl<'a, 'db> OpportunisticRegionResolver<'a, 'db> {
    pub fn new(infcx: &'a InferCtxt<'db>) -> Self {
        OpportunisticRegionResolver { infcx }
    }
}

impl<'a, 'db> TypeFolder<DbInterner<'db>> for OpportunisticRegionResolver<'a, 'db> {
    fn cx(&self) -> DbInterner<'db> {
        self.infcx.interner
    }

    fn fold_ty(&mut self, t: Ty<'db>) -> Ty<'db> {
        if !t.has_infer_regions() {
            t // micro-optimize -- if there is nothing in this type that this fold affects...
        } else {
            t.super_fold_with(self)
        }
    }

    fn fold_region(&mut self, r: Region<'db>) -> Region<'db> {
        match r.clone().kind() {
            RegionKind::ReVar(vid) => self
                .infcx
                .inner
                .borrow_mut()
                .unwrap_region_constraints()
                .opportunistic_resolve_var(self.infcx.interner, vid),
            _ => r,
        }
    }

    fn fold_const(&mut self, ct: Const<'db>) -> Const<'db> {
        if !ct.has_infer_regions() {
            ct // micro-optimize -- if there is nothing in this const that this fold affects...
        } else {
            ct.super_fold_with(self)
        }
    }
}

///////////////////////////////////////////////////////////////////////////
// FULL TYPE RESOLUTION

/// Full type resolution replaces all type and region variables with
/// their concrete results. If any variable cannot be replaced (never unified, etc)
/// then an `Err` result is returned.
pub fn fully_resolve<'db, T>(infcx: &InferCtxt<'db>, value: T) -> FixupResult<T>
where
    T: TypeFoldable<DbInterner<'db>>,
{
    value.try_fold_with(&mut FullTypeResolver { infcx })
}

struct FullTypeResolver<'a, 'db> {
    infcx: &'a InferCtxt<'db>,
}

impl<'a, 'db> FallibleTypeFolder<DbInterner<'db>> for FullTypeResolver<'a, 'db> {
    type Error = FixupError;

    fn cx(&self) -> DbInterner<'db> {
        self.infcx.interner
    }

    fn try_fold_ty(&mut self, t: Ty<'db>) -> Result<Ty<'db>, Self::Error> {
        if !t.has_infer() {
            Ok(t) // micro-optimize -- if there is nothing in this type that this fold affects...
        } else {
            use super::TyOrConstInferVar::*;

            let t = self.infcx.shallow_resolve(t);
            match t.clone().kind() {
                TyKind::Infer(InferTy::TyVar(vid)) => Err(FixupError { unresolved: Ty(vid) }),
                TyKind::Infer(InferTy::IntVar(vid)) => Err(FixupError { unresolved: TyInt(vid) }),
                TyKind::Infer(InferTy::FloatVar(vid)) => {
                    Err(FixupError { unresolved: TyFloat(vid) })
                }
                TyKind::Infer(_) => {
                    panic!("Unexpected type in full type resolver: {:?}", t);
                }
                _ => t.try_super_fold_with(self),
            }
        }
    }

    fn try_fold_region(&mut self, r: Region<'db>) -> Result<Region<'db>, Self::Error> {
        match r {
            /*
            RegionKind::ReVar(_) => Ok(self
                .infcx
                .lexical_region_resolutions
                .borrow()
                .as_ref()
                .expect("region resolution not performed")
                .resolve_region(self.infcx.tcx, r)),
            */
            _ => Ok(r),
        }
    }

    fn try_fold_const(&mut self, c: Const<'db>) -> Result<Const<'db>, Self::Error> {
        if !c.has_infer() {
            Ok(c) // micro-optimize -- if there is nothing in this const that this fold affects...
        } else {
            let c = self.infcx.shallow_resolve_const(c);
            match c.clone().kind() {
                ConstKind::Infer(InferConst::Var(vid)) => {
                    return Err(FixupError { unresolved: super::TyOrConstInferVar::Const(vid) });
                }
                ConstKind::Infer(InferConst::Fresh(_)) => {
                    panic!("Unexpected const in full const resolver: {:?}", c);
                }
                _ => {}
            }
            c.try_super_fold_with(self)
        }
    }
}
