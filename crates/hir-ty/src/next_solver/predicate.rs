use rustc_type_ir::{
    self as ty,
    elaborate::Elaboratable,
    fold::{TypeFoldable, TypeSuperFoldable},
    inherent::IntoKind,
    relate::Relate,
    visit::{Flags, TypeSuperVisitable, TypeVisitable},
    Binder, ClauseKind, PredicateKind, UpcastFrom,
};

use super::{
    BoundExistentialPredicates, Clause, Clauses, DbInterner, ParamEnv, Predicate, Region, Ty,
};

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
        todo!()
    }

    fn caller_bounds(
        self,
    ) -> impl IntoIterator<Item = <DbInterner as rustc_type_ir::Interner>::Clause> {
        [todo!()]
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
        todo!()
    }

    fn child(&self, clause: <DbInterner as rustc_type_ir::Interner>::Clause) -> Self {
        todo!()
    }

    fn child_with_derived_cause(
        &self,
        clause: <DbInterner as rustc_type_ir::Interner>::Clause,
        span: <DbInterner as rustc_type_ir::Interner>::Span,
        parent_trait_pred: rustc_type_ir::Binder<
            DbInterner,
            rustc_type_ir::TraitPredicate<DbInterner>,
        >,
        index: usize,
    ) -> Self {
        todo!()
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
    type Kind = Binder<DbInterner, PredicateKind<DbInterner>>;

    fn kind(self) -> Self::Kind {
        todo!()
    }
}

impl UpcastFrom<DbInterner, ty::PredicateKind<DbInterner>> for Predicate {
    fn upcast_from(from: ty::PredicateKind<DbInterner>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::PredicateKind<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::PredicateKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::ClauseKind<DbInterner>> for Predicate {
    fn upcast_from(from: ty::ClauseKind<DbInterner>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, Clause> for Predicate {
    fn upcast_from(from: Clause, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::NormalizesTo<DbInterner>> for Predicate {
    fn upcast_from(from: ty::NormalizesTo<DbInterner>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::TraitRef<DbInterner>> for Predicate {
    fn upcast_from(from: ty::TraitRef<DbInterner>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitRef<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitRef<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::TraitPredicate<DbInterner>> for Predicate {
    fn upcast_from(from: ty::TraitPredicate<DbInterner>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::OutlivesPredicate<DbInterner, Ty>> for Predicate {
    fn upcast_from(from: ty::OutlivesPredicate<DbInterner, Ty>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::OutlivesPredicate<DbInterner, Region>> for Predicate {
    fn upcast_from(from: ty::OutlivesPredicate<DbInterner, Region>, interner: DbInterner) -> Self {
        todo!()
    }
}

impl rustc_type_ir::inherent::Predicate<DbInterner> for Predicate {
    fn as_clause(self) -> Option<<DbInterner as rustc_type_ir::Interner>::Clause> {
        todo!()
    }

    fn is_coinductive(self, interner: DbInterner) -> bool {
        todo!()
    }

    fn allow_normalization(self) -> bool {
        todo!()
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
    type Kind = Binder<DbInterner, ClauseKind<DbInterner>>;

    fn kind(self) -> Self::Kind {
        todo!()
    }
}

impl Elaboratable<DbInterner> for Clause {
    fn predicate(&self) -> <DbInterner as rustc_type_ir::Interner>::Predicate {
        todo!()
    }

    fn child(&self, clause: <DbInterner as rustc_type_ir::Interner>::Clause) -> Self {
        todo!()
    }

    fn child_with_derived_cause(
        &self,
        clause: <DbInterner as rustc_type_ir::Interner>::Clause,
        span: <DbInterner as rustc_type_ir::Interner>::Span,
        parent_trait_pred: rustc_type_ir::Binder<
            DbInterner,
            rustc_type_ir::TraitPredicate<DbInterner>,
        >,
        index: usize,
    ) -> Self {
        todo!()
    }
}

impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::TraitRef<DbInterner>> for Clause {
    fn upcast_from(from: ty::TraitRef<DbInterner>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitRef<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitRef<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::TraitPredicate<DbInterner>> for Clause {
    fn upcast_from(from: ty::TraitPredicate<DbInterner>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitPredicate<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitPredicate<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::ProjectionPredicate<DbInterner>> for Clause {
    fn upcast_from(from: ty::ProjectionPredicate<DbInterner>, interner: DbInterner) -> Self {
        todo!()
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ProjectionPredicate<DbInterner>>>
    for Clause
{
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ProjectionPredicate<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        todo!()
    }
}

impl rustc_type_ir::inherent::Clause<DbInterner> for Clause {
    fn instantiate_supertrait(
        self,
        cx: DbInterner,
        trait_ref: rustc_type_ir::Binder<DbInterner, rustc_type_ir::TraitRef<DbInterner>>,
    ) -> Self {
        todo!()
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
