use chalk_ir::interner::HasInterner;

use crate::{db::HirDatabase, mapping::ToChalk};

use super::{Canonical, Goal, Predicate, Ty};

// TODO reusing ToChalk for this might not work, we might need more context?

impl ToChalk for Ty {
    type Chalk = crate::Ty;

    fn to_chalk(self, db: &dyn HirDatabase) -> Self::Chalk {
        todo!()
    }

    fn from_chalk(db: &dyn HirDatabase, chalk: Self::Chalk) -> Self {
        todo!()
    }
}

impl<T: ToChalk<Chalk: HasInterner<Interner = crate::Interner>>> ToChalk for Canonical<T> {
    type Chalk = crate::Canonical<T::Chalk>;

    fn to_chalk(self, db: &dyn HirDatabase) -> Self::Chalk {
        todo!()
    }

    fn from_chalk(db: &dyn HirDatabase, chalk: Self::Chalk) -> Self {
        todo!()
    }
}

impl ToChalk for Goal<Predicate> {
    type Chalk = crate::Goal;

    fn to_chalk(self, db: &dyn HirDatabase) -> Self::Chalk {
        todo!()
    }

    fn from_chalk(db: &dyn HirDatabase, chalk: Self::Chalk) -> Self {
        todo!()
    }
}
