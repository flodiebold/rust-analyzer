macro_rules! bug {
    ($($tt:tt)*) => { panic!($($tt)*) }
}
macro_rules! span_bug {
    ($span:expr, $($tt:tt)*) => { panic!($($tt)*) }
}

mod rustc_mir {
    pub use crate::mir::*;
    pub type BasicBlock<'db> = BasicBlockId<'db>;
    pub type BasicBlockData<'db> = crate::mir::BasicBlock<'db>;
    pub type Body<'db> = crate::mir::MirBody<'db>;
    pub type Local<'db> = crate::mir::LocalId<'db>;
}

mod un_derefer;
mod move_paths;
