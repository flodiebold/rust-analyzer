//! Freshening is the process of replacing unknown variables with fresh types. The idea is that
//! the type, after freshening, contains no inference variables but instead contains either a
//! value for each variable or fresh "arbitrary" types wherever a variable would have been.
//!
//! Freshening is used primarily to get a good type for inserting into a cache. The result
//! summarizes what the type inferencer knows "so far". The primary place it is used right now is
//! in the trait matching algorithm, which needs to be able to cache whether an `impl` self type
//! matches some other type X -- *without* affecting `X`. That means that if the type `X` is in
//! fact an unbound type variable, we want the match to be regarded as ambiguous, because depending
//! on what type that type variable is ultimately assigned, the match may or may not succeed.
//!
//! To handle closures, freshened types also have to contain the signature and kind of any
//! closure in the local inference context, as otherwise the cache key might be invalidated.
//! The way this is done is somewhat hacky - the closure signature is appended to the args,
//! as well as the closure kind "encoded" as a type. Also, special handling is needed when
//! the closure signature contains a reference to the original closure.
//!
//! Note that you should be careful not to allow the output of freshening to leak to the user in
//! error messages or in any other form. Freshening is only really useful as an internal detail.
//!
//! Because of the manipulation required to handle closures, doing arbitrary operations on
//! freshened types is not recommended. However, in addition to doing equality/hash
//! comparisons (for caching), it is possible to do a `_match` operation between
//! two freshened types - this works even with the closure encoding.
//!
//! __An important detail concerning regions.__ The freshener also replaces *all* free regions with
//! 'erased. The reason behind this is that, in general, we do not take region relationships into
//! account when making type-overloaded decisions. This is important because of the design of the
//! region inferencer, which is not based on unification but rather on accumulating and then
//! solving a set of constraints. In contrast, the type inferencer assigns a value to each type
//! variable only once, and it does so as soon as it can, so it is reasonable to ask what the type
//! inferencer knows "so far".

use std::collections::hash_map::Entry;

use rustc_hash::FxHashMap;
use rustc_type_ir::{
    ConstKind, FloatVarValue, InferConst, InferTy, IntVarValue, RegionKind, TyKind, TypeFoldable,
    TypeFolder, TypeSuperFoldable, TypeVisitableExt,
    inherent::{Const as _, IntoKind},
};

use crate::next_solver::{Const, DbInterner, Region, Ty};

use super::InferCtxt;

pub struct TypeFreshener<'a, 'db> {
    infcx: &'a InferCtxt<'db>,
    ty_freshen_count: u32,
    const_freshen_count: u32,
    ty_freshen_map: FxHashMap<InferTy, Ty<'db>>,
    const_freshen_map: FxHashMap<InferConst, Const<'db>>,
}

impl<'a, 'db> TypeFreshener<'a, 'db> {
    pub fn new(infcx: &'a InferCtxt<'db>) -> TypeFreshener<'a, 'db> {
        TypeFreshener {
            infcx,
            ty_freshen_count: 0,
            const_freshen_count: 0,
            ty_freshen_map: Default::default(),
            const_freshen_map: Default::default(),
        }
    }

    fn freshen_ty<F>(&mut self, input: Result<Ty<'db>, InferTy>, mk_fresh: F) -> Ty<'db>
    where
        F: FnOnce(u32) -> Ty<'db>,
    {
        match input {
            Ok(ty) => ty.fold_with(self),
            Err(key) => match self.ty_freshen_map.entry(key) {
                Entry::Occupied(entry) => entry.get().clone(),
                Entry::Vacant(entry) => {
                    let index = self.ty_freshen_count;
                    self.ty_freshen_count += 1;
                    let t = mk_fresh(index);
                    entry.insert(t.clone());
                    t
                }
            },
        }
    }

    fn freshen_const<F>(
        &mut self,
        input: Result<Const<'db>, InferConst>,
        freshener: F,
    ) -> Const<'db>
    where
        F: FnOnce(u32) -> InferConst,
    {
        match input {
            Ok(ct) => ct.fold_with(self),
            Err(key) => match self.const_freshen_map.entry(key) {
                Entry::Occupied(entry) => entry.get().clone(),
                Entry::Vacant(entry) => {
                    let index = self.const_freshen_count;
                    self.const_freshen_count += 1;
                    let ct = Const::new_infer(self.infcx.interner, freshener(index));
                    entry.insert(ct.clone());
                    ct
                }
            },
        }
    }
}

impl<'a, 'db> TypeFolder<DbInterner<'db>> for TypeFreshener<'a, 'db> {
    fn cx(&self) -> DbInterner<'db> {
        self.infcx.interner
    }

    fn fold_region(&mut self, r: Region<'db>) -> Region<'db> {
        match r.clone().kind() {
            RegionKind::ReBound(..) => {
                // leave bound regions alone
                r
            }

            RegionKind::ReEarlyParam(..)
            | RegionKind::ReLateParam(_)
            | RegionKind::ReVar(_)
            | RegionKind::RePlaceholder(..)
            | RegionKind::ReStatic
            | RegionKind::ReError(_)
            | RegionKind::ReErased => Region::new(self.cx(), RegionKind::ReErased),
        }
    }

    #[inline]
    fn fold_ty(&mut self, t: Ty<'db>) -> Ty<'db> {
        if !t.has_infer() && !t.has_erasable_regions() {
            t
        } else {
            match t.clone().kind() {
                TyKind::Infer(v) => self.fold_infer_ty(v).unwrap_or(t),

                // This code is hot enough that a non-debug assertion here makes a noticeable
                // difference on benchmarks like `wg-grammar`.
                #[cfg(debug_assertions)]
                TyKind::Placeholder(..) | TyKind::Bound(..) => panic!("unexpected type {:?}", t),

                _ => t.super_fold_with(self),
            }
        }
    }

    fn fold_const(&mut self, ct: Const<'db>) -> Const<'db> {
        match ct.clone().kind() {
            ConstKind::Infer(InferConst::Var(v)) => {
                let mut inner = self.infcx.inner.borrow_mut();
                let input =
                    inner.const_unification_table().probe_value(v).known().ok_or_else(|| {
                        InferConst::Var(inner.const_unification_table().find(v).vid)
                    });
                drop(inner);
                self.freshen_const(input, InferConst::Fresh)
            }
            ConstKind::Infer(InferConst::Fresh(i)) => {
                if i >= self.const_freshen_count {
                    panic!(
                        "Encountered a freshend const with id {} \
                            but our counter is only at {}",
                        i, self.const_freshen_count,
                    );
                }
                ct
            }

            ConstKind::Bound(..) | ConstKind::Placeholder(_) => {
                panic!("unexpected const {:?}", ct)
            }

            ConstKind::Param(_)
            | ConstKind::Value(_)
            | ConstKind::Unevaluated(..)
            | ConstKind::Expr(..)
            | ConstKind::Error(_) => ct.super_fold_with(self),
        }
    }
}

impl<'a, 'db> TypeFreshener<'a, 'db> {
    // This is separate from `fold_ty` to keep that method small and inlinable.
    #[inline(never)]
    fn fold_infer_ty(&mut self, v: InferTy) -> Option<Ty<'db>> {
        match v {
            InferTy::TyVar(v) => {
                let mut inner = self.infcx.inner.borrow_mut();
                let input = inner
                    .type_variables()
                    .probe(v)
                    .known()
                    .ok_or_else(|| InferTy::TyVar(inner.type_variables().root_var(v)));
                drop(inner);
                Some(self.freshen_ty(input, |n| Ty::new_fresh(self.infcx.interner, n)))
            }

            InferTy::IntVar(v) => {
                let mut inner = self.infcx.inner.borrow_mut();
                let value = inner.int_unification_table().probe_value(v);
                let input = match value {
                    IntVarValue::IntType(ty) => Ok(Ty::new_int(self.infcx.interner, ty)),
                    IntVarValue::UintType(ty) => Ok(Ty::new_uint(self.infcx.interner, ty)),
                    IntVarValue::Unknown => {
                        Err(InferTy::IntVar(inner.int_unification_table().find(v)))
                    }
                };
                drop(inner);
                Some(self.freshen_ty(input, |n| Ty::new_fresh_int(self.infcx.interner, n)))
            }

            InferTy::FloatVar(v) => {
                let mut inner = self.infcx.inner.borrow_mut();
                let value = inner.float_unification_table().probe_value(v);
                let input = match value {
                    FloatVarValue::Known(ty) => Ok(Ty::new_float(self.infcx.interner, ty)),
                    FloatVarValue::Unknown => {
                        Err(InferTy::FloatVar(inner.float_unification_table().find(v)))
                    }
                };
                drop(inner);
                Some(self.freshen_ty(input, |n| Ty::new_fresh_float(self.infcx.interner, n)))
            }

            InferTy::FreshTy(ct) | InferTy::FreshIntTy(ct) | InferTy::FreshFloatTy(ct) => {
                if ct >= self.ty_freshen_count {
                    panic!(
                        "Encountered a freshend type with id {} \
                          but our counter is only at {}",
                        ct, self.ty_freshen_count
                    );
                }
                None
            }
        }
    }
}
