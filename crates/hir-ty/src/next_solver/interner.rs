use std::marker::PhantomData;

use base_db::{
    impl_intern_key,
    salsa::{self, InternId, InternValueTrivial},
};
use hir_def::hir::PatId;
use rustc_type_ir::{
    relate::Relate,
    solve::{ExternalConstraintsData, PredefinedOpaquesData},
    Binder, BoundVar, CanonicalVarInfo, EarlyBinder, ExistentialPredicate, Interner, RegionKind,
    UniverseIndex, Variance,
};
use scoped_tls::scoped_thread_local;

use crate::{db::HirDatabase, FnAbi};

macro_rules! interned_vec {
    ($name:ident, $ty:ty) => {
        paste::paste! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct [<Interned $name>](Vec<$ty>);
            impl InternValueTrivial for [<Interned $name>] {}

            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub struct $name(salsa::InternId);
            impl_intern_key!($name);

            impl rustc_type_ir::inherent::SliceLike for $name {
                type Item = $ty;

                type IntoIter = <[$ty; 0] as IntoIterator>::IntoIter;

                fn iter(self) -> Self::IntoIter {
                    todo!()
                }

                fn as_slice(&self) -> &[Self::Item] {
                    todo!()
                }
            }

            impl Default for $name {
                fn default() -> Self {
                    todo!()
                }
            }


            impl rustc_type_ir::relate::Relate<DbInterner> for $name {
                fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(relation: &mut R, a: Self, b: Self) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
                    todo!()
                }
            }

            impl rustc_type_ir::fold::TypeFoldable<DbInterner> for $name {
                fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(self, folder: &mut F) -> Result<Self, F::Error> {
                    todo!()
                }
            }

            impl rustc_type_ir::visit::TypeVisitable<DbInterner> for $name {
                fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(&self, visitor: &mut V) -> V::Result {
                    todo!()
                }
            }
        }
    };
    ($name:ident, $ty:ty, slice) => {
        interned_vec!($name, $ty);

        paste::paste! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub struct [<$name Slice>]($name, usize, usize);

            impl rustc_type_ir::inherent::SliceLike for [<$name Slice>] {
                type Item = $ty;

                type IntoIter = <[$ty; 0] as IntoIterator>::IntoIter;

                fn iter(self) -> Self::IntoIter {
                    todo!()
                }

                fn as_slice(&self) -> &[Self::Item] {
                    todo!()
                }
            }

            impl rustc_type_ir::visit::TypeVisitable<DbInterner> for [<$name Slice>] {
                fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(&self, visitor: &mut V) -> V::Result {
                    todo!()
                }
            }
        }
    };
}

macro_rules! interned_struct {
    ($name:ident, $ty:ty) => {
        paste::paste! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct [<Interned $name>]($ty);
            impl InternValueTrivial for [<Interned $name>] {}

            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub struct $name(salsa::InternId);
            impl_intern_key!($name);

            impl [<Interned $name>] {
                pub(super) fn inner(self) -> $ty { self.0 }
            }
        }
    };
}

macro_rules! salsa_intern_things {
    ($($name:ident),+) => {
                paste::paste! {
        #[salsa::query_group(RustcInternDatabaseStorage)]
        pub trait RustcInternDb {
            $(
                    #[salsa::interned]
                    fn [<intern_rustc_ $name:snake>](&self, content: self::[<Interned $name>]) -> self::$name;
            )*
        }
                }
    }
}

// Interned things for new type IR / trait solver
salsa_intern_things![
    GenericArgs,
    BoundVarKinds,
    PredefinedOpaques,
    DefiningOpaqueTypes,
    CanonicalVars,
    ExternalConstraints,
    Ty,
    Tys,
    BoundExistentialPredicates,
    Const,
    Predicate,
    Clause,
    Variances
];

interned_vec!(GenericArgs, GenericArg, slice);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(Ty),
    Lifetime(Region),
    Const(Const),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Term {
    Ty(Ty),
    Const(Const),
}

interned_vec!(BoundVarKinds, BoundVarKind);

interned_struct!(PredefinedOpaques, PredefinedOpaquesData<DbInterner>);

interned_vec!(DefiningOpaqueTypes, DefId);
interned_vec!(CanonicalVars, CanonicalVarInfo<DbInterner>);
interned_struct!(ExternalConstraints, ExternalConstraintsData<DbInterner>);

interned_struct!(Ty, rustc_type_ir::TyKind<DbInterner>);
interned_vec!(Tys, Ty, slice);

interned_vec!(BoundExistentialPredicates, BoundExistentialPredicate);

interned_struct!(Const, rustc_type_ir::ConstKind<DbInterner>);

interned_struct!(Predicate, rustc_type_ir::Binder<DbInterner, rustc_type_ir::PredicateKind<DbInterner>>);

interned_struct!(Clause, rustc_type_ir::Binder<DbInterner, rustc_type_ir::ClauseKind<DbInterner>>);
interned_vec!(Clauses, Clause);

interned_vec!(Variances, Variance);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(InternId);

impl rustc_type_ir::inherent::DefId<DbInterner> for DefId {
    fn is_local(self) -> bool {
        true // TODO
    }

    fn as_local(self) -> Option<DefId> {
        Some(self) // TODO
    }
}

macro_rules! TrivialTypeTraversalImpls {
    ($($ty:ty,)+) => {
        $(
            impl rustc_type_ir::fold::TypeFoldable<DbInterner> for $ty {
                fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
                    self,
                    _: &mut F,
                ) -> ::std::result::Result<Self, F::Error> {
                    Ok(self)
                }

                #[inline]
                fn fold_with<F: rustc_type_ir::fold::TypeFolder<DbInterner>>(
                    self,
                    _: &mut F,
                ) -> Self {
                    self
                }
            }

            impl rustc_type_ir::visit::TypeVisitable<DbInterner> for $ty {
                #[inline]
                fn visit_with<F: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
                    &self,
                    _: &mut F)
                    -> F::Result
                {
                    <F::Result as rustc_ast_ir::visit::VisitorResult>::output()
                }
            }
        )+
    };
}

TrivialTypeTraversalImpls! { DefId, PatId, Safety, FnAbi, Span, }

#[derive(Clone, Copy)]
pub struct DbInterner {
    // pub(super) db: &'db dyn HirDatabase,
    _marker: PhantomData<*const dyn HirDatabase>,
}

impl Interner for DbInterner {
    type DefId = DefId;
    // TODO do we need to distinguish between local and non-local def ids
    // if so, we probably need to store the crate in the interner?
    type LocalDefId = DefId;
    type Span = Span;

    type GenericArgs = GenericArgs;
    type GenericArgsSlice = GenericArgsSlice;
    type GenericArg = GenericArg;
    type Term = Term;

    type BoundVarKinds = BoundVarKinds;
    type BoundVarKind = BoundVarKind;

    type PredefinedOpaques = PredefinedOpaques;

    fn mk_predefined_opaques_in_body(
        self,
        data: rustc_type_ir::solve::PredefinedOpaquesData<Self>,
    ) -> Self::PredefinedOpaques {
        self.with_db(|db| db.intern_rustc_predefined_opaques(InternedPredefinedOpaques(data)))
    }

    type DefiningOpaqueTypes = DefiningOpaqueTypes;

    type CanonicalVars = CanonicalVars;

    fn mk_canonical_var_infos(
        self,
        infos: &[rustc_type_ir::CanonicalVarInfo<Self>],
    ) -> Self::CanonicalVars {
        self.with_db(|db| db.intern_rustc_canonical_vars(InternedCanonicalVars(infos.to_vec())))
    }

    type ExternalConstraints = ExternalConstraints;

    fn mk_external_constraints(
        self,
        data: rustc_type_ir::solve::ExternalConstraintsData<Self>,
    ) -> Self::ExternalConstraints {
        self.with_db(|db| db.intern_rustc_external_constraints(InternedExternalConstraints(data)))
    }

    // TODO what exactly do we need to do here
    type DepNodeIndex = ();
    type Tracked<T: std::fmt::Debug + Clone> = T;

    fn mk_tracked<T: std::fmt::Debug + Clone>(
        self,
        data: T,
        dep_node: Self::DepNodeIndex,
    ) -> Self::Tracked<T> {
        data
    }

    fn get_tracked<T: std::fmt::Debug + Clone>(self, tracked: &Self::Tracked<T>) -> T {
        tracked.clone()
    }

    fn with_cached_task<T>(self, task: impl FnOnce() -> T) -> (T, Self::DepNodeIndex) {
        (task(), ())
    }

    type Ty = Ty;
    type Tys = Tys;
    type FnInputTys = TysSlice;
    type ParamTy = ParamTy;
    type BoundTy = BoundTy;
    type PlaceholderTy = PlaceholderType;

    type ErrorGuaranteed = ErrorGuaranteed;
    type BoundExistentialPredicates = BoundExistentialPredicates;

    type AllocId = ();
    type Pat = PatId;
    type Safety = Safety;
    type Abi = FnAbi;

    type Const = Const;
    type PlaceholderConst = PlaceholderConst;
    type ParamConst = ParamConst;
    type BoundConst = BoundVar;
    type ValueConst = ValueConst;
    type ExprConst = ExprConst;

    type Region = Region;
    type EarlyParamRegion = EarlyParamRegion;
    type LateParamRegion = LateParamRegion;
    type BoundRegion = BoundRegion;
    type PlaceholderRegion = PlaceholderRegion;

    type ParamEnv = ParamEnv;
    type Predicate = Predicate;
    type Clause = Clause;
    type Clauses = Clauses;

    fn with_global_cache<R>(
        self,
        mode: rustc_type_ir::solve::SolverMode,
        f: impl FnOnce(&mut rustc_type_ir::search_graph::GlobalCache<Self>) -> R,
    ) -> R {
        todo!()
    }

    fn evaluation_is_concurrent(&self) -> bool {
        todo!()
    }

    fn expand_abstract_consts<T: rustc_type_ir::fold::TypeFoldable<Self>>(self, t: T) -> T {
        todo!()
    }

    type GenericsOf = Generics;

    fn generics_of(self, def_id: Self::DefId) -> Self::GenericsOf {
        todo!()
    }

    type VariancesOf = Variances;

    fn variances_of(self, def_id: Self::DefId) -> Self::VariancesOf {
        todo!()
    }

    fn type_of(self, def_id: Self::DefId) -> rustc_type_ir::EarlyBinder<Self, Self::Ty> {
        todo!()
    }

    type AdtDef = AdtDef;

    fn adt_def(self, adt_def_id: Self::DefId) -> Self::AdtDef {
        todo!()
    }

    fn alias_ty_kind(self, alias: rustc_type_ir::AliasTy<Self>) -> rustc_type_ir::AliasTyKind {
        todo!()
    }

    fn alias_term_kind(
        self,
        alias: rustc_type_ir::AliasTerm<Self>,
    ) -> rustc_type_ir::AliasTermKind {
        todo!()
    }

    fn trait_ref_and_own_args_for_alias(
        self,
        def_id: Self::DefId,
        args: Self::GenericArgs,
    ) -> (rustc_type_ir::TraitRef<Self>, Self::GenericArgsSlice) {
        todo!()
    }

    fn mk_args(self, args: &[Self::GenericArg]) -> Self::GenericArgs {
        todo!()
    }

    fn mk_args_from_iter<I, T>(self, args: I) -> T::Output
    where
        I: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<Self::GenericArg, Self::GenericArgs>,
    {
        todo!()
    }

    fn check_args_compatible(self, def_id: Self::DefId, args: Self::GenericArgs) -> bool {
        todo!()
    }

    fn debug_assert_args_compatible(self, def_id: Self::DefId, args: Self::GenericArgs) {
        todo!()
    }

    fn mk_type_list_from_iter<I, T>(self, args: I) -> T::Output
    where
        I: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<Self::Ty, Self::Tys>,
    {
        todo!()
    }

    fn parent(self, def_id: Self::DefId) -> Self::DefId {
        todo!()
    }

    fn recursion_limit(self) -> usize {
        todo!()
    }

    type Features = Features;

    fn features(self) -> Self::Features {
        todo!()
    }

    fn bound_coroutine_hidden_types(
        self,
        def_id: Self::DefId,
    ) -> impl IntoIterator<Item = rustc_type_ir::EarlyBinder<Self, rustc_type_ir::Binder<Self, Self::Ty>>>
    {
        [todo!()]
    }

    fn fn_sig(
        self,
        def_id: Self::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self, rustc_type_ir::Binder<Self, rustc_type_ir::FnSig<Self>>>
    {
        todo!()
    }

    fn coroutine_movability(self, def_id: Self::DefId) -> rustc_ast_ir::Movability {
        todo!()
    }

    fn coroutine_for_closure(self, def_id: Self::DefId) -> Self::DefId {
        todo!()
    }

    fn generics_require_sized_self(self, def_id: Self::DefId) -> bool {
        todo!()
    }

    fn item_bounds(
        self,
        def_id: Self::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>> {
        EarlyBinder::bind([todo!()])
    }

    fn predicates_of(
        self,
        def_id: Self::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>> {
        EarlyBinder::bind([todo!()])
    }

    fn own_predicates_of(
        self,
        def_id: Self::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>> {
        EarlyBinder::bind([todo!()])
    }

    fn explicit_super_predicates_of(
        self,
        def_id: Self::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self, impl IntoIterator<Item = (Self::Clause, Self::Span)>>
    {
        EarlyBinder::bind([todo!()])
    }

    fn explicit_implied_predicates_of(
        self,
        def_id: Self::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self, impl IntoIterator<Item = (Self::Clause, Self::Span)>>
    {
        EarlyBinder::bind([todo!()])
    }

    fn has_target_features(self, def_id: Self::DefId) -> bool {
        todo!()
    }

    fn require_lang_item(
        self,
        lang_item: rustc_type_ir::lang_items::TraitSolverLangItem,
    ) -> Self::DefId {
        todo!()
    }

    fn is_lang_item(
        self,
        def_id: Self::DefId,
        lang_item: rustc_type_ir::lang_items::TraitSolverLangItem,
    ) -> bool {
        todo!()
    }

    fn as_lang_item(
        self,
        def_id: Self::DefId,
    ) -> Option<rustc_type_ir::lang_items::TraitSolverLangItem> {
        todo!()
    }

    fn associated_type_def_ids(self, def_id: Self::DefId) -> impl IntoIterator<Item = Self::DefId> {
        [todo!()]
    }

    fn for_each_relevant_impl(
        self,
        trait_def_id: Self::DefId,
        self_ty: Self::Ty,
        f: impl FnMut(Self::DefId),
    ) {
        todo!()
    }

    fn has_item_definition(self, def_id: Self::DefId) -> bool {
        todo!()
    }

    fn impl_is_default(self, impl_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn impl_trait_ref(
        self,
        impl_def_id: Self::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self, rustc_type_ir::TraitRef<Self>> {
        todo!()
    }

    fn impl_polarity(self, impl_def_id: Self::DefId) -> rustc_type_ir::ImplPolarity {
        todo!()
    }

    fn trait_is_auto(self, trait_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn trait_is_alias(self, trait_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn trait_is_object_safe(self, trait_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn trait_is_fundamental(self, def_id: Self::DefId) -> bool {
        todo!()
    }

    fn trait_may_be_implemented_via_object(self, trait_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn delay_bug(self, msg: impl ToString) -> Self::ErrorGuaranteed {
        todo!()
    }

    fn is_general_coroutine(self, coroutine_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn coroutine_is_async(self, coroutine_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn coroutine_is_gen(self, coroutine_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn coroutine_is_async_gen(self, coroutine_def_id: Self::DefId) -> bool {
        todo!()
    }

    fn layout_is_pointer_like(self, param_env: Self::ParamEnv, ty: Self::Ty) -> bool {
        todo!()
    }

    type UnsizingParams = UnsizingParams;

    fn unsizing_params_for_adt(self, adt_def_id: Self::DefId) -> Self::UnsizingParams {
        todo!()
    }

    fn find_const_ty_from_env(
        self,
        param_env: Self::ParamEnv,
        placeholder: Self::PlaceholderConst,
    ) -> Self::Ty {
        todo!()
    }

    fn anonymize_bound_vars<T: rustc_type_ir::fold::TypeFoldable<Self>>(
        self,
        binder: rustc_type_ir::Binder<Self, T>,
    ) -> rustc_type_ir::Binder<Self, T> {
        todo!()
    }
}

impl DbInterner {
    pub(super) fn mk_ty(self, kind: rustc_type_ir::TyKind<DbInterner>) -> Ty {
        self.with_db(|db| db.intern_rustc_ty(InternedTy(kind)))
    }
}

scoped_thread_local!(static DB: *const dyn HirDatabase);

// TODO: think about safety here
/// This should be the only way to get an Interner from outside?
pub fn with_interner<T>(db: &dyn HirDatabase, f: impl FnOnce(DbInterner) -> T) -> T {
    DB.set(
        &(unsafe { std::mem::transmute::<_, &'static dyn HirDatabase>(db) }
            as *const dyn HirDatabase),
        move || {
            let i = DbInterner { _marker: PhantomData };
            f(i)
        },
    )
}

impl DbInterner {
    pub(super) fn with_db<T>(self, f: impl FnOnce(&dyn HirDatabase) -> T) -> T {
        DB.with(move |slot| f(unsafe { &**slot }))
    }
}

#[deprecated]
pub(super) fn with_db_out_of_thin_air<T>(f: impl FnOnce(&dyn HirDatabase) -> T) -> T {
    DB.with(move |slot| f(unsafe { &**slot }))
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct Span;

pub type BoundExistentialPredicate = Binder<DbInterner, ExistentialPredicate<DbInterner>>;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BoundVarKind {
    Ty(BoundTyKind),
    Region(BoundRegionKind),
    Const,
}

impl BoundVarKind {
    pub fn expect_region(self) -> BoundRegionKind {
        match self {
            BoundVarKind::Region(lt) => lt,
            _ => panic!("expected a region, but found another kind"),
        }
    }

    pub fn expect_ty(self) -> BoundTyKind {
        match self {
            BoundVarKind::Ty(ty) => ty,
            _ => panic!("expected a type, but found another kind"),
        }
    }

    pub fn expect_const(self) {
        match self {
            BoundVarKind::Const => (),
            _ => panic!("expected a const, but found another kind"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)] // FIXME implement by hand
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] // FIXME implement by hand
pub struct BoundTy {
    pub var: rustc_type_ir::BoundVar,
    pub kind: BoundTyKind,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BoundTyKind {
    Anon,
    Param(DefId, Symbol),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)] // FIXME implement by hand
pub struct Placeholder<T> {
    pub universe: UniverseIndex,
    pub bound: T,
}

pub type PlaceholderType = Placeholder<BoundTy>;
pub type PlaceholderRegion = Placeholder<BoundRegion>;
pub type PlaceholderConst = Placeholder<BoundVar>;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Region {
    pub kind: RegionKind<DbInterner>,
}

pub(crate) type DebruijnIndex = u32;

type Symbol = ();

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct EarlyParamRegion {
    pub index: u32,
    pub name: Symbol,
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

#[derive(Clone, PartialEq, Eq, Hash, Copy, Debug)] // FIXME implement manually
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

#[derive(Clone, PartialEq, Eq, Hash, Copy, Debug)] // FIXME implement manually
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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ErrorGuaranteed;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Safety {
    Unsafe,
    Safe,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)] // FIXME implement manually
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

impl rustc_type_ir::inherent::ParamLike for ParamConst {
    fn index(self) -> u32 {
        self.index
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct ValueConst;
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct ExprConst;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct ParamEnv;

pub struct Generics;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct AdtDef(hir_def::AdtId);

impl rustc_type_ir::inherent::AdtDef<DbInterner> for AdtDef {
    fn def_id(self) -> <DbInterner as Interner>::DefId {
        todo!()
    }

    fn is_struct(self) -> bool {
        todo!()
    }

    fn struct_tail_ty(
        self,
        interner: DbInterner,
    ) -> Option<rustc_type_ir::EarlyBinder<DbInterner, <DbInterner as Interner>::Ty>> {
        todo!()
    }

    fn is_phantom_data(self) -> bool {
        todo!()
    }

    fn all_field_tys(
        self,
        interner: DbInterner,
    ) -> rustc_type_ir::EarlyBinder<
        DbInterner,
        impl IntoIterator<Item = <DbInterner as Interner>::Ty>,
    > {
        EarlyBinder::bind([todo!()])
    }

    fn sized_constraint(
        self,
        interner: DbInterner,
    ) -> Option<rustc_type_ir::EarlyBinder<DbInterner, <DbInterner as Interner>::Ty>> {
        todo!()
    }

    fn is_fundamental(self) -> bool {
        todo!()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Features;

impl rustc_type_ir::inherent::Features<DbInterner> for Features {
    fn generic_const_exprs(self) -> bool {
        todo!()
    }

    fn coroutine_clone(self) -> bool {
        todo!()
    }

    fn associated_const_equality(self) -> bool {
        todo!()
    }
}

pub struct UnsizingParams(rustc_index::bit_set::BitSet<u32>);

impl std::ops::Deref for UnsizingParams {
    type Target = rustc_index::bit_set::BitSet<u32>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Relate<DbInterner> for PatId {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        todo!()
    }
}

impl rustc_type_ir::inherent::GenericsOf<DbInterner> for Generics {
    fn count(&self) -> usize {
        todo!()
    }
}
