use rustc_type_ir::{
    self as ty,
    elaborate::Elaboratable,
    fold::{TypeFoldable, TypeSuperFoldable},
    inherent::{IntoKind, SliceLike},
    relate::Relate,
    solve::Reveal,
    visit::{Flags, TypeSuperVisitable, TypeVisitable},
    EarlyBinder, Upcast, UpcastFrom,
};

use super::{with_db_out_of_thin_air, Binder, DbInterner, Region, Ty};

pub type BoundExistentialPredicate = Binder<ExistentialPredicate>;

pub type TraitRef = ty::TraitRef<DbInterner>;
pub type AliasTerm = ty::AliasTerm<DbInterner>;
pub type ProjectionPredicate = ty::ProjectionPredicate<DbInterner>;
pub type ExistentialPredicate = ty::ExistentialPredicate<DbInterner>;
pub type ExistentialTraitRef = ty::ExistentialTraitRef<DbInterner>;
pub type ExistentialProjection = ty::ExistentialProjection<DbInterner>;
pub type TraitPredicate = ty::TraitPredicate<DbInterner>;
pub type ClauseKind = ty::ClauseKind<DbInterner>;
pub type PredicateKind = ty::PredicateKind<DbInterner>;
pub type NormalizesTo = ty::NormalizesTo<DbInterner>;
pub type CoercePredicate = ty::CoercePredicate<DbInterner>;
pub type SubtypePredicate = ty::SubtypePredicate<DbInterner>;
pub type OutlivesPredicate<T> = ty::OutlivesPredicate<DbInterner, T>;
pub type RegionOutlivesPredicate = OutlivesPredicate<Region>;
pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;
pub type PolyTraitPredicate = Binder<TraitPredicate>;
pub type PolyRegionOutlivesPredicate = Binder<RegionOutlivesPredicate>;
pub type PolyTypeOutlivesPredicate = Binder<TypeOutlivesPredicate>;
pub type PolySubtypePredicate = Binder<SubtypePredicate>;
pub type PolyCoercePredicate = Binder<CoercePredicate>;
pub type PolyProjectionPredicate = Binder<ProjectionPredicate>;

interned_vec!(BoundExistentialPredicates, BoundExistentialPredicate);

interned_struct!(Predicate, Binder<rustc_type_ir::PredicateKind<DbInterner>>);

interned_vec!(Clauses, Clause);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] // TODO implement Debug by hand
pub struct Clause(Predicate);

// We could cram the reveal into the clauses like rustc does, probably
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct ParamEnv {
    pub(super) reveal: Reveal,
    pub(super) clauses: Clauses,
}

impl rustc_type_ir::inherent::BoundExistentialPredicates<DbInterner>
    for BoundExistentialPredicates
{
    fn principal_def_id(self) -> Option<<DbInterner as rustc_type_ir::Interner>::DefId> {
        todo!()
    }

    fn principal(
        self,
    ) -> Option<rustc_type_ir::Binder<DbInterner, rustc_type_ir::ExistentialTraitRef<DbInterner>>>
    {
        todo!()
    }

    fn auto_traits(
        self,
    ) -> impl IntoIterator<Item = <DbInterner as rustc_type_ir::Interner>::DefId> {
        [todo!()]
    }

    fn projection_bounds(
        self,
    ) -> impl IntoIterator<
        Item = rustc_type_ir::Binder<DbInterner, rustc_type_ir::ExistentialProjection<DbInterner>>,
    > {
        [todo!()]
    }
}

impl TypeVisitable<DbInterner> for ParamEnv {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for ParamEnv {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl rustc_type_ir::inherent::ParamEnv<DbInterner> for ParamEnv {
    fn reveal(self) -> rustc_type_ir::solve::Reveal {
        self.reveal
    }

    fn caller_bounds(
        self,
    ) -> impl IntoIterator<Item = <DbInterner as rustc_type_ir::Interner>::Clause> {
        self.clauses.iter()
    }
}

impl TypeVisitable<DbInterner> for Predicate {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeSuperVisitable<DbInterner> for Predicate {
    fn super_visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for Predicate {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl TypeSuperFoldable<DbInterner> for Predicate {
    fn try_super_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl Elaboratable<DbInterner> for Predicate {
    fn predicate(&self) -> <DbInterner as rustc_type_ir::Interner>::Predicate {
        *self
    }

    fn child(&self, clause: <DbInterner as rustc_type_ir::Interner>::Clause) -> Self {
        clause.as_predicate()
    }

    fn child_with_derived_cause(
        &self,
        clause: <DbInterner as rustc_type_ir::Interner>::Clause,
        _span: <DbInterner as rustc_type_ir::Interner>::Span,
        _parent_trait_pred: rustc_type_ir::Binder<
            DbInterner,
            rustc_type_ir::TraitPredicate<DbInterner>,
        >,
        _index: usize,
    ) -> Self {
        clause.as_predicate()
    }
}

impl Flags for Predicate {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        todo!()
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        todo!()
    }
}

impl IntoKind for Predicate {
    type Kind = Binder<PredicateKind>;

    fn kind(self) -> Self::Kind {
        with_db_out_of_thin_air(|db| db.lookup_intern_rustc_predicate(self).0)
    }
}

impl UpcastFrom<DbInterner, ty::PredicateKind<DbInterner>> for Predicate {
    fn upcast_from(from: ty::PredicateKind<DbInterner>, interner: DbInterner) -> Self {
        Binder::dummy(from).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::PredicateKind<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::PredicateKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        interner.with_db(|db| db.intern_rustc_predicate(InternedPredicate(from)))
    }
}
impl UpcastFrom<DbInterner, ty::ClauseKind<DbInterner>> for Predicate {
    fn upcast_from(from: ty::ClauseKind<DbInterner>, interner: DbInterner) -> Self {
        Binder::dummy(PredicateKind::Clause(from)).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        from.map_bound(PredicateKind::Clause).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, Clause> for Predicate {
    fn upcast_from(from: Clause, _interner: DbInterner) -> Self {
        from.0
    }
}
impl UpcastFrom<DbInterner, ty::NormalizesTo<DbInterner>> for Predicate {
    fn upcast_from(from: ty::NormalizesTo<DbInterner>, interner: DbInterner) -> Self {
        PredicateKind::NormalizesTo(from).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::TraitRef<DbInterner>> for Predicate {
    fn upcast_from(from: ty::TraitRef<DbInterner>, interner: DbInterner) -> Self {
        Binder::dummy(from).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitRef<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitRef<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        let pred: PolyTraitPredicate = from.upcast(interner);
        pred.upcast(interner)
    }
}
impl UpcastFrom<DbInterner, Binder<ty::TraitPredicate<DbInterner>>> for Predicate {
    fn upcast_from(from: Binder<ty::TraitPredicate<DbInterner>>, interner: DbInterner) -> Self {
        from.map_bound(|it| PredicateKind::Clause(ClauseKind::Trait(it))).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, Binder<ProjectionPredicate>> for Predicate {
    fn upcast_from(from: Binder<ProjectionPredicate>, interner: DbInterner) -> Self {
        from.map_bound(|it| PredicateKind::Clause(ClauseKind::Projection(it))).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ProjectionPredicate> for Predicate {
    fn upcast_from(from: ProjectionPredicate, interner: DbInterner) -> Self {
        PredicateKind::Clause(ClauseKind::Projection(from)).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::TraitPredicate<DbInterner>> for Predicate {
    fn upcast_from(from: ty::TraitPredicate<DbInterner>, interner: DbInterner) -> Self {
        PredicateKind::Clause(ClauseKind::Trait(from)).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::OutlivesPredicate<DbInterner, Ty>> for Predicate {
    fn upcast_from(from: ty::OutlivesPredicate<DbInterner, Ty>, interner: DbInterner) -> Self {
        PredicateKind::Clause(ClauseKind::TypeOutlives(from)).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::OutlivesPredicate<DbInterner, Region>> for Predicate {
    fn upcast_from(from: ty::OutlivesPredicate<DbInterner, Region>, interner: DbInterner) -> Self {
        PredicateKind::Clause(ClauseKind::RegionOutlives(from)).upcast(interner)
    }
}

impl rustc_type_ir::inherent::Predicate<DbInterner> for Predicate {
    fn as_clause(self) -> Option<<DbInterner as rustc_type_ir::Interner>::Clause> {
        match self.kind().skip_binder() {
            PredicateKind::Clause(..) => Some(self.expect_clause()),
            _ => None,
        }
    }

    fn is_coinductive(self, interner: DbInterner) -> bool {
        match self.kind().skip_binder() {
            ty::PredicateKind::Clause(ty::ClauseKind::Trait(data)) => {
                todo!()
                // tcx.trait_is_coinductive(data.def_id())
            }
            ty::PredicateKind::Clause(ty::ClauseKind::WellFormed(_)) => true,
            _ => false,
        }
    }

    /// Whether this projection can be soundly normalized.
    ///
    /// Wf predicates must not be normalized, as normalization
    /// can remove required bounds which would cause us to
    /// unsoundly accept some programs. See #91068.
    fn allow_normalization(self) -> bool {
        // TODO: this should probably live in rustc_type_ir
        match self.kind().skip_binder() {
            PredicateKind::Clause(ClauseKind::WellFormed(_))
            | PredicateKind::AliasRelate(..)
            | PredicateKind::NormalizesTo(..) => false,
            PredicateKind::Clause(ClauseKind::Trait(_))
            | PredicateKind::Clause(ClauseKind::RegionOutlives(_))
            | PredicateKind::Clause(ClauseKind::TypeOutlives(_))
            | PredicateKind::Clause(ClauseKind::Projection(_))
            | PredicateKind::Clause(ClauseKind::ConstArgHasType(..))
            | PredicateKind::ObjectSafe(_)
            | PredicateKind::Subtype(_)
            | PredicateKind::Coerce(_)
            | PredicateKind::Clause(ClauseKind::ConstEvaluatable(_))
            | PredicateKind::ConstEquate(_, _)
            | PredicateKind::Ambiguous => true,
        }
    }
}

impl Predicate {
    /// Assert that the predicate is a clause.
    pub fn expect_clause(self) -> Clause {
        match self.kind().skip_binder() {
            PredicateKind::Clause(..) => Clause(self),
            _ => panic!("{self:?} is not a clause"),
        }
    }
}

impl TypeVisitable<DbInterner> for Clause {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl TypeFoldable<DbInterner> for Clause {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl IntoKind for Clause {
    type Kind = Binder<ClauseKind>;

    fn kind(self) -> Self::Kind {
        self.0.kind().map_bound(|pk| match pk {
            PredicateKind::Clause(kind) => kind,
            _ => unreachable!(),
        })
    }
}

impl Clause {
    pub fn as_predicate(self) -> Predicate {
        self.0
    }
}

impl Elaboratable<DbInterner> for Clause {
    fn predicate(&self) -> <DbInterner as rustc_type_ir::Interner>::Predicate {
        self.as_predicate()
    }

    fn child(&self, clause: <DbInterner as rustc_type_ir::Interner>::Clause) -> Self {
        clause
    }

    fn child_with_derived_cause(
        &self,
        clause: <DbInterner as rustc_type_ir::Interner>::Clause,
        _span: <DbInterner as rustc_type_ir::Interner>::Span,
        _parent_trait_pred: rustc_type_ir::Binder<
            DbInterner,
            rustc_type_ir::TraitPredicate<DbInterner>,
        >,
        _index: usize,
    ) -> Self {
        clause
    }
}

impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Clause(from.map_bound(PredicateKind::Clause).upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::TraitRef<DbInterner>> for Clause {
    fn upcast_from(from: ty::TraitRef<DbInterner>, interner: DbInterner) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitRef<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitRef<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::TraitPredicate<DbInterner>> for Clause {
    fn upcast_from(from: ty::TraitPredicate<DbInterner>, interner: DbInterner) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitPredicate<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitPredicate<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::ProjectionPredicate<DbInterner>> for Clause {
    fn upcast_from(from: ty::ProjectionPredicate<DbInterner>, interner: DbInterner) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ProjectionPredicate<DbInterner>>>
    for Clause
{
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ProjectionPredicate<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}

impl rustc_type_ir::inherent::Clause<DbInterner> for Clause {
    fn instantiate_supertrait(
        self,
        cx: DbInterner,
        trait_ref: rustc_type_ir::Binder<DbInterner, rustc_type_ir::TraitRef<DbInterner>>,
    ) -> Self {
        // See the rustc impl for a long comment
        let bound_pred = self.kind();
        let pred_bound_vars = bound_pred.bound_vars();
        let trait_bound_vars = trait_ref.bound_vars();
        // 1) Self: Bar1<'a, '^0.0> -> Self: Bar1<'a, '^0.1>
        let shifted_pred =
            cx.shift_bound_var_indices(trait_bound_vars.len(), bound_pred.skip_binder());
        // 2) Self: Bar1<'a, '^0.1> -> T: Bar1<'^0.0, '^0.1>
        let new = EarlyBinder::bind(shifted_pred).instantiate(cx, trait_ref.skip_binder().args);
        // 3) ['x] + ['b] -> ['x, 'b]
        let bound_vars =
            cx.mk_bound_variable_kinds_from_iter(trait_bound_vars.iter().chain(pred_bound_vars));

        // FIXME: Is it really perf sensitive to use reuse_or_mk_predicate here?
        let predicate: Predicate =
            ty::Binder::bind_with_vars(PredicateKind::Clause(new), bound_vars).upcast(cx);
        predicate.expect_clause()
    }
}

impl TypeSuperVisitable<DbInterner> for Clauses {
    fn super_visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

impl Flags for Clauses {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        todo!()
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        todo!()
    }
}
