#[macro_use]
mod interner;
mod abi;
mod consts;
mod generic_arg;
mod infer;
mod ir_print;
mod lifetime;
mod mapping;
mod opaques;
mod predicate;
mod solver;
mod ty;

pub type Binder<T> = rustc_type_ir::Binder<DbInterner, T>;

// TODO use actual interned names?
type Symbol = ();

pub use abi::Safety;
pub use consts::{Const, ExprConst, ParamConst, PlaceholderConst, UnevaluatedConst, ValueConst};
pub use generic_arg::{GenericArg, GenericArgs, GenericArgsSlice, Term};
pub use infer::{Canonical, CanonicalVarInfo, CanonicalVarValues};
pub use interner::*;
pub use lifetime::{
    BoundRegion, BoundRegionKind, EarlyParamRegion, LateParamRegion, PlaceholderRegion, Region,
};
pub use opaques::{DefiningOpaqueTypes, ExternalConstraints, OpaqueTypeKey, PredefinedOpaques};
pub use predicate::{
    BoundExistentialPredicate, BoundExistentialPredicates, Clause, Clauses, OutlivesPredicate,
    ParamEnv, PolyCoercePredicate, Predicate, SubtypePredicate, TraitRef, TypeOutlivesPredicate,
};
pub use solver::Goal;
pub use ty::{BoundTy, BoundTyKind, ErrorGuaranteed, ParamTy, PlaceholderTy, Ty, Tys, TysSlice};
