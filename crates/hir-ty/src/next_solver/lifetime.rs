use rustc_type_ir::{
    fold::TypeFoldable,
    inherent::{IntoKind, PlaceholderLike},
    relate::Relate,
    visit::{Flags, TypeVisitable},
    BoundVar, RegionKind,
};

use super::{BoundVarKind, DbInterner, DefId, Placeholder, Symbol};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Region {
    pub kind: RegionKind<DbInterner>,
}

pub type PlaceholderRegion = Placeholder<BoundRegion>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct EarlyParamRegion {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Clone, PartialEq, Eq, Hash, Copy, Debug)] // FIXME implement Debug manually
/// The parameter representation of late-bound function parameters, "some region
/// at least as big as the scope `fr.scope`".
///
/// Similar to a placeholder region as we create `LateParam` regions when entering a binder
/// except they are always in the root universe and instead of using a boundvar to distinguish
/// between others we use the `DefId` of the parameter. For this reason the `bound_region` field
/// should basically always be `BoundRegionKind::BrNamed` as otherwise there is no way of telling
/// different parameters apart.
pub struct LateParamRegion {
    pub scope: DefId,
    pub bound_region: BoundRegionKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Copy, Debug)] // FIXME implement Debug manually
pub enum BoundRegionKind {
    /// An anonymous region parameter for a given fn (&T)
    BrAnon,

    /// Named region parameters for functions (a in &'a T)
    ///
    /// The `DefId` is needed to distinguish free regions in
    /// the event of shadowing.
    BrNamed(DefId, Symbol),

    /// Anonymous region for the implicit env pointer parameter
    /// to a closure
    BrEnv,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

impl rustc_type_ir::inherent::ParamLike for EarlyParamRegion {
    fn index(self) -> u32 {
        self.index
    }
}

impl std::fmt::Debug for EarlyParamRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.index)
        // write!(f, "{}/#{}", self.name, self.index)
    }
}

impl rustc_type_ir::inherent::BoundVarLike<DbInterner> for BoundRegion {
    fn var(self) -> BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        assert_eq!(self.kind, var.expect_region())
    }
}

impl core::fmt::Debug for BoundRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            BoundRegionKind::BrAnon => write!(f, "{:?}", self.var),
            BoundRegionKind::BrEnv => write!(f, "{:?}.Env", self.var),
            BoundRegionKind::BrNamed(def, symbol) => {
                write!(f, "{:?}.Named({:?}, {:?})", self.var, def, symbol)
            }
        }
    }
}

impl BoundRegionKind {
    pub fn is_named(&self) -> bool {
        match *self {
            BoundRegionKind::BrNamed(_, name) => {
                true
                // name != kw::UnderscoreLifetime && name != kw::Empty
            }
            _ => false,
        }
    }

    pub fn get_name(&self) -> Option<Symbol> {
        if self.is_named() {
            match *self {
                BoundRegionKind::BrNamed(_, name) => return Some(name),
                _ => unreachable!(),
            }
        }

        None
    }

    pub fn get_id(&self) -> Option<DefId> {
        match *self {
            BoundRegionKind::BrNamed(id, _) => Some(id),
            _ => None,
        }
    }
}

impl IntoKind for Region {
    type Kind = RegionKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        self.kind
    }
}

impl TypeVisitable<DbInterner> for Region {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for Region {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl Relate<DbInterner> for Region {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        todo!()
    }
}

impl Flags for Region {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        todo!()
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        todo!()
    }
}

impl rustc_type_ir::inherent::Region<DbInterner> for Region {
    fn new_bound(
        _interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: BoundRegion,
    ) -> Self {
        Region { kind: RegionKind::ReBound(debruijn, var) }
    }

    fn new_anon_bound(
        _interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: rustc_type_ir::BoundVar,
    ) -> Self {
        Region {
            kind: RegionKind::ReBound(debruijn, BoundRegion { var, kind: BoundRegionKind::BrAnon }),
        }
    }

    fn new_static(_interner: DbInterner) -> Self {
        Region { kind: RegionKind::ReStatic }
    }
}

impl PlaceholderLike for PlaceholderRegion {
    fn universe(self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(self) -> rustc_type_ir::BoundVar {
        self.bound.var
    }

    fn with_updated_universe(self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, ..self }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, var: rustc_type_ir::BoundVar) -> Self {
        Placeholder { universe: ui, bound: BoundRegion { var, kind: BoundRegionKind::BrAnon } }
    }
}
