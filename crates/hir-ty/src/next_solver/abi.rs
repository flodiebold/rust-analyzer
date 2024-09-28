use rustc_type_ir::{error::TypeError, relate::Relate};

use crate::FnAbi;

use super::DbInterner;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Safety {
    Unsafe,
    Safe,
}

impl Relate<DbInterner> for Safety {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        _relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        if a != b {
            Err(TypeError::SafetyMismatch(rustc_type_ir::error::ExpectedFound::new(true, a, b)))
        } else {
            Ok(a)
        }
    }
}

impl rustc_type_ir::inherent::Safety<DbInterner> for Safety {
    fn safe() -> Self {
        Self::Safe
    }

    fn is_safe(self) -> bool {
        matches!(self, Safety::Safe)
    }

    fn prefix_str(self) -> &'static str {
        match self {
            Self::Unsafe => "unsafe ",
            Self::Safe => "",
        }
    }
}

impl Relate<DbInterner> for FnAbi {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        _relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        if a == b {
            Ok(a)
        } else {
            Err(TypeError::AbiMismatch(rustc_type_ir::error::ExpectedFound::new(true, a, b)))
        }
    }
}

impl rustc_type_ir::inherent::Abi<DbInterner> for FnAbi {
    fn rust() -> Self {
        FnAbi::Rust
    }

    fn is_rust(self) -> bool {
        matches!(self, FnAbi::Rust)
    }
}
