#[macro_use]
mod interner;
mod abi;
mod consts;
mod generic_arg;
mod ir_print;
mod lifetime;
mod opaques;
mod predicate;
mod ty;

pub type Binder<T> = rustc_type_ir::Binder<DbInterner, T>;

// TODO use actual interned names?
type Symbol = ();

pub use abi::Safety;
pub use consts::{Const, ExprConst, ParamConst, PlaceholderConst, ValueConst};
pub use generic_arg::{GenericArg, GenericArgs, GenericArgsSlice, Term};
pub use interner::*;
pub use lifetime::{
    BoundRegion, BoundRegionKind, EarlyParamRegion, LateParamRegion, PlaceholderRegion, Region,
};
pub use predicate::{
    BoundExistentialPredicate, BoundExistentialPredicates, Clause, Clauses, ParamEnv, Predicate,
};
pub use ty::{BoundTy, BoundTyKind, ErrorGuaranteed, ParamTy, PlaceholderTy, Ty, Tys, TysSlice};
