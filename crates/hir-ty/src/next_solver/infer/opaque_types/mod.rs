use std::sync::Arc;

use tracing::{debug, instrument};

use crate::next_solver::{
    Clause, ClauseKind, FxIndexMap, GenericArgs, OpaqueTypeKey, ProjectionPredicate, SolverDefId,
    TypingMode, util::BottomUpFolder,
};

mod table;

pub(crate) type OpaqueTypeMap<'db> = FxIndexMap<OpaqueTypeKey<'db>, OpaqueTypeDecl<'db>>;
pub(crate) use table::{OpaqueTypeStorage, OpaqueTypeTable};

use crate::next_solver::{
    AliasTy, Binder, BoundRegion, BoundTy, Canonical, CanonicalVarValues, Const, DbInterner, DbIr,
    Goal, ParamEnv, Predicate, PredicateKind, Region, Span, Ty, TyKind,
    fold::FnMutDelegate,
    infer::{
        DefineOpaqueTypes, InferCtxt, SubregionOrigin, TypeTrace,
        traits::{Obligation, PredicateObligations},
    },
};
use rustc_type_ir::{
    AliasRelationDirection, AliasTyKind, BoundConstness, BoundVar, Flags, GenericArgKind, InferTy,
    Interner, RegionKind, TypeFlags, TypeFoldable, TypeSuperVisitable, TypeVisitable,
    TypeVisitableExt, TypeVisitor, Upcast, Variance,
    error::{ExpectedFound, TypeError},
    inherent::{DefId, GenericArgs as _, IntoKind, SliceLike},
    relate::{
        Relate, TypeRelation, VarianceDiagInfo,
        combine::{super_combine_consts, super_combine_tys},
    },
};

use super::{InferOk, traits::ObligationCause};

#[derive(Clone, Debug)]
pub struct OpaqueHiddenType<'db> {
    pub ty: Ty<'db>,
}

/// Information about the opaque types whose values we
/// are inferring in this function (these are the `impl Trait` that
/// appear in the return type).
#[derive(Clone, Debug)]
pub struct OpaqueTypeDecl<'db> {
    /// The hidden types that have been inferred for this opaque type.
    /// There can be multiple, but they are all `lub`ed together at the end
    /// to obtain the canonical hidden type.
    pub hidden_type: OpaqueHiddenType<'db>,
}

impl<'db> InferCtxt<'db> {
    /// This is a backwards compatibility hack to prevent breaking changes from
    /// lazy TAIT around RPIT handling.
    pub fn replace_opaque_types_with_inference_vars<T: TypeFoldable<DbInterner<'db>>>(
        &self,
        value: T,
        body_id: SolverDefId,
        span: Span,
        param_env: ParamEnv<'db>,
    ) -> InferOk<'db, T> {
        // We handle opaque types differently in the new solver.
        return InferOk { value, obligations: PredicateObligations::from_iter([]) };
    }

    pub fn handle_opaque_type(
        &self,
        a: Ty<'db>,
        b: Ty<'db>,
        span: Span,
        param_env: ParamEnv<'db>,
    ) -> Result<Vec<Goal<'db, Predicate<'db>>>, TypeError<DbInterner<'db>>> {
        let process = |a: Ty<'db>, b: Ty<'db>| match a.kind() {
            TyKind::Alias(AliasTyKind::Opaque, AliasTy { def_id, args, .. })
                if def_id.is_local() =>
            {
                let def_id = def_id.as_local().unwrap();
                if let TypingMode::Coherence = self.typing_mode() {
                    // See comment on `insert_hidden_type` for why this is sufficient in coherence
                    return Some(self.register_hidden_type(
                        OpaqueTypeKey { def_id, args },
                        span,
                        param_env.clone(),
                        b,
                    ));
                }
                // Check that this is `impl Trait` type is
                // declared by `parent_def_id` -- i.e., one whose
                // value we are inferring. At present, this is
                // always true during the first phase of
                // type-check, but not always true later on during
                // NLL. Once we support named opaque types more fully,
                // this same scenario will be able to arise during all phases.
                //
                // Here is an example using type alias `impl Trait`
                // that indicates the distinction we are checking for:
                //
                // ```rust
                // mod a {
                //   pub type Foo = impl Iterator;
                //   pub fn make_foo() -> Foo { .. }
                // }
                //
                // mod b {
                //   fn foo() -> a::Foo { a::make_foo() }
                // }
                // ```
                //
                // Here, the return type of `foo` references an
                // `Opaque` indeed, but not one whose value is
                // presently being inferred. You can get into a
                // similar situation with closure return types
                // today:
                //
                // ```rust
                // fn foo() -> impl Iterator { .. }
                // fn bar() {
                //     let x = || foo(); // returns the Opaque assoc with `foo`
                // }
                // ```
                if !self.can_define_opaque_ty(def_id) {
                    return None;
                }

                if let TyKind::Alias(AliasTyKind::Opaque, AliasTy { def_id: b_def_id, .. }) =
                    b.clone().kind()
                {
                    // We could accept this, but there are various ways to handle this situation,
                    // and we don't want to make a decision on it right now. Likely this case is so
                    // super rare anyway, that no one encounters it in practice. It does occur
                    // however in `fn fut() -> impl Future<Output = i32> { async { 42 } }`, where
                    // it is of no concern, so we only check for TAITs.
                    /*
                    if self.can_define_opaque_ty(b_def_id)
                        && matches!(
                            self.tcx.opaque_ty_origin(b_def_id),
                            hir::OpaqueTyOrigin::TyAlias { .. }
                        )
                    {
                        self.dcx().emit_err(OpaqueHiddenTypeDiag {
                            span,
                            hidden_type: self.tcx.def_span(b_def_id),
                            opaque_type: self.tcx.def_span(def_id),
                        });
                    }
                    */
                }
                Some(self.register_hidden_type(
                    OpaqueTypeKey { def_id, args },
                    span,
                    param_env.clone(),
                    b,
                ))
            }
            _ => None,
        };
        if let Some(res) = process(a.clone(), b.clone()) {
            res
        } else if let Some(res) = process(b.clone(), a.clone()) {
            res
        } else {
            let (a, b) = self.resolve_vars_if_possible((a, b));
            Err(TypeError::Sorts(ExpectedFound::new(a, b)))
        }
    }

    /// Given the map `opaque_types` containing the opaque
    /// `impl Trait` types whose underlying, hidden types are being
    /// inferred, this method adds constraints to the regions
    /// appearing in those underlying hidden types to ensure that they
    /// at least do not refer to random scopes within the current
    /// function. These constraints are not (quite) sufficient to
    /// guarantee that the regions are actually legal values; that
    /// final condition is imposed after region inference is done.
    ///
    /// # The Problem
    ///
    /// Let's work through an example to explain how it works. Assume
    /// the current function is as follows:
    ///
    /// ```text
    /// fn foo<'a, 'b>(..) -> (impl Bar<'a>, impl Bar<'b>)
    /// ```
    ///
    /// Here, we have two `impl Trait` types whose values are being
    /// inferred (the `impl Bar<'a>` and the `impl
    /// Bar<'b>`). Conceptually, this is sugar for a setup where we
    /// define underlying opaque types (`Foo1`, `Foo2`) and then, in
    /// the return type of `foo`, we *reference* those definitions:
    ///
    /// ```text
    /// type Foo1<'x> = impl Bar<'x>;
    /// type Foo2<'x> = impl Bar<'x>;
    /// fn foo<'a, 'b>(..) -> (Foo1<'a>, Foo2<'b>) { .. }
    ///                    //  ^^^^ ^^
    ///                    //  |    |
    ///                    //  |    args
    ///                    //  def_id
    /// ```
    ///
    /// As indicating in the comments above, each of those references
    /// is (in the compiler) basically generic parameters (`args`)
    /// applied to the type of a suitable `def_id` (which identifies
    /// `Foo1` or `Foo2`).
    ///
    /// Now, at this point in compilation, what we have done is to
    /// replace each of the references (`Foo1<'a>`, `Foo2<'b>`) with
    /// fresh inference variables C1 and C2. We wish to use the values
    /// of these variables to infer the underlying types of `Foo1` and
    /// `Foo2`. That is, this gives rise to higher-order (pattern) unification
    /// constraints like:
    ///
    /// ```text
    /// for<'a> (Foo1<'a> = C1)
    /// for<'b> (Foo1<'b> = C2)
    /// ```
    ///
    /// For these equation to be satisfiable, the types `C1` and `C2`
    /// can only refer to a limited set of regions. For example, `C1`
    /// can only refer to `'static` and `'a`, and `C2` can only refer
    /// to `'static` and `'b`. The job of this function is to impose that
    /// constraint.
    ///
    /// Up to this point, C1 and C2 are basically just random type
    /// inference variables, and hence they may contain arbitrary
    /// regions. In fact, it is fairly likely that they do! Consider
    /// this possible definition of `foo`:
    ///
    /// ```text
    /// fn foo<'a, 'b>(x: &'a i32, y: &'b i32) -> (impl Bar<'a>, impl Bar<'b>) {
    ///         (&*x, &*y)
    ///     }
    /// ```
    ///
    /// Here, the values for the concrete types of the two impl
    /// traits will include inference variables:
    ///
    /// ```text
    /// &'0 i32
    /// &'1 i32
    /// ```
    ///
    /// Ordinarily, the subtyping rules would ensure that these are
    /// sufficiently large. But since `impl Bar<'a>` isn't a specific
    /// type per se, we don't get such constraints by default. This
    /// is where this function comes into play. It adds extra
    /// constraints to ensure that all the regions which appear in the
    /// inferred type are regions that could validly appear.
    ///
    /// This is actually a bit of a tricky constraint in general. We
    /// want to say that each variable (e.g., `'0`) can only take on
    /// values that were supplied as arguments to the opaque type
    /// (e.g., `'a` for `Foo1<'a>`) or `'static`, which is always in
    /// scope. We don't have a constraint quite of this kind in the current
    /// region checker.
    ///
    /// # The Solution
    ///
    /// We generally prefer to make `<=` constraints, since they
    /// integrate best into the region solver. To do that, we find the
    /// "minimum" of all the arguments that appear in the args: that
    /// is, some region which is less than all the others. In the case
    /// of `Foo1<'a>`, that would be `'a` (it's the only choice, after
    /// all). Then we apply that as a least bound to the variables
    /// (e.g., `'a <= '0`).
    ///
    /// In some cases, there is no minimum. Consider this example:
    ///
    /// ```text
    /// fn baz<'a, 'b>() -> impl Trait<'a, 'b> { ... }
    /// ```
    ///
    /// Here we would report a more complex "in constraint", like `'r
    /// in ['a, 'b, 'static]` (where `'r` is some region appearing in
    /// the hidden type).
    ///
    /// # Constrain regions, not the hidden concrete type
    ///
    /// Note that generating constraints on each region `Rc` is *not*
    /// the same as generating an outlives constraint on `Tc` itself.
    /// For example, if we had a function like this:
    ///
    /// ```
    /// # #![feature(type_alias_impl_trait)]
    /// # fn main() {}
    /// # trait Foo<'a> {}
    /// # impl<'a, T> Foo<'a> for (&'a u32, T) {}
    /// fn foo<'a, T>(x: &'a u32, y: T) -> impl Foo<'a> {
    ///   (x, y)
    /// }
    ///
    /// // Equivalent to:
    /// # mod dummy { use super::*;
    /// type FooReturn<'a, T> = impl Foo<'a>;
    /// fn foo<'a, T>(x: &'a u32, y: T) -> FooReturn<'a, T> {
    ///   (x, y)
    /// }
    /// # }
    /// ```
    ///
    /// then the hidden type `Tc` would be `(&'0 u32, T)` (where `'0`
    /// is an inference variable). If we generated a constraint that
    /// `Tc: 'a`, then this would incorrectly require that `T: 'a` --
    /// but this is not necessary, because the opaque type we
    /// create will be allowed to reference `T`. So we only generate a
    /// constraint that `'0: 'a`.
    #[instrument(level = "debug", skip(self))]
    pub fn register_member_constraints(
        &self,
        opaque_type_key: OpaqueTypeKey<'db>,
        concrete_ty: Ty<'db>,
        span: Span,
    ) {
        let concrete_ty = self.resolve_vars_if_possible(concrete_ty);
        debug!(?concrete_ty);

        let variances = self.interner.variances_of(opaque_type_key.def_id);
        debug!(?variances);

        // For a case like `impl Foo<'a, 'b>`, we would generate a constraint
        // `'r in ['a, 'b, 'static]` for each region `'r` that appears in the
        // hidden type (i.e., it must be equal to `'a`, `'b`, or `'static`).
        //
        // `conflict1` and `conflict2` are the two region bounds that we
        // detected which were unrelated. They are used for diagnostics.

        // Create the set of choice regions: each region in the hidden
        // type can be equal to any of the region parameters of the
        // opaque type definition.
        let choice_regions: Arc<Vec<Region<'db>>> = Arc::new(
            opaque_type_key
                .args
                .clone()
                .iter()
                .enumerate()
                .filter(|(i, _)| variances.as_slice()[*i] == Variance::Invariant)
                .filter_map(|(_, arg)| match arg.kind() {
                    GenericArgKind::Lifetime(r) => Some(r),
                    GenericArgKind::Type(_) | GenericArgKind::Const(_) => None,
                })
                .chain(std::iter::once(Region::new(self.interner, RegionKind::ReStatic)))
                .collect(),
        );

        // FIXME(#42940): This should use the `FreeRegionsVisitor`, but that's
        // not currently sound until we have existential regions.
        concrete_ty.visit_with(&mut ConstrainOpaqueTypeRegionVisitor {
            tcx: self.interner,
            op: |r| {
                self.member_constraint(
                    opaque_type_key.clone(),
                    span,
                    concrete_ty.clone(),
                    r,
                    Arc::clone(&choice_regions),
                )
            },
        });
    }
}

/// Visitor that requires that (almost) all regions in the type visited outlive
/// `least_region`. We cannot use `push_outlives_components` because regions in
/// closure signatures are not included in their outlives components. We need to
/// ensure all regions outlive the given bound so that we don't end up with,
/// say, `ReVar` appearing in a return type and causing ICEs when other
/// functions end up with region constraints involving regions from other
/// functions.
///
/// We also cannot use `for_each_free_region` because for closures it includes
/// the regions parameters from the enclosing item.
///
/// We ignore any type parameters because impl trait values are assumed to
/// capture all the in-scope type parameters.
struct ConstrainOpaqueTypeRegionVisitor<'db, OP: FnMut(Region<'db>)> {
    tcx: DbInterner<'db>,
    op: OP,
}

impl<'db, OP> TypeVisitor<DbInterner<'db>> for ConstrainOpaqueTypeRegionVisitor<'db, OP>
where
    OP: FnMut(Region<'db>),
{
    type Result = ();

    fn visit_binder<T: TypeVisitable<DbInterner<'db>>>(&mut self, t: &Binder<'db, T>) {
        t.super_visit_with(self);
    }

    fn visit_region(&mut self, r: Region<'db>) {
        match r.clone().kind() {
            // ignore bound regions, keep visiting
            RegionKind::ReBound(_, _) => {}
            _ => (self.op)(r),
        }
    }

    fn visit_ty(&mut self, ty: Ty<'db>) {
        // We're only interested in types involving regions
        if !ty.flags().intersects(TypeFlags::HAS_FREE_REGIONS) {
            return;
        }

        match ty.clone().kind() {
            TyKind::Closure(_, args) => {
                // Skip lifetime parameters of the enclosing item(s)

                for upvar in args.clone().as_closure().upvar_tys() {
                    upvar.visit_with(self);
                }
                args.as_closure().sig_as_fn_ptr_ty().visit_with(self);
            }

            TyKind::CoroutineClosure(_, args) => {
                // Skip lifetime parameters of the enclosing item(s)

                for upvar in args.clone().as_coroutine_closure().upvar_tys() {
                    upvar.visit_with(self);
                }

                args.as_coroutine_closure().signature_parts_ty().visit_with(self);
            }

            TyKind::Coroutine(_, args) => {
                // Skip lifetime parameters of the enclosing item(s)
                // Also skip the witness type, because that has no free regions.

                for upvar in args.clone().as_coroutine().upvar_tys() {
                    upvar.visit_with(self);
                }
                args.clone().as_coroutine().return_ty().visit_with(self);
                args.clone().as_coroutine().yield_ty().visit_with(self);
                args.clone().as_coroutine().resume_ty().visit_with(self);
            }

            TyKind::Alias(AliasTyKind::Opaque, AliasTy { def_id, args, .. }) => {
                // Skip lifetime parameters that are not captures.
                /*
                let variances = self.tcx.variances_of(*def_id);

                for (v, s) in std::iter::zip(variances, args.iter()) {
                    if *v != Variance::Bivariant {
                        s.visit_with(self);
                    }
                }
                */
                for s in args.iter() {
                    s.visit_with(self);
                }
            }

            _ => {
                ty.super_visit_with(self);
            }
        }
    }
}

impl<'db> InferCtxt<'db> {
    #[instrument(skip(self), level = "debug")]
    fn register_hidden_type(
        &self,
        opaque_type_key: OpaqueTypeKey<'db>,
        span: Span,
        param_env: ParamEnv<'db>,
        hidden_ty: Ty<'db>,
    ) -> Result<Vec<Goal<'db, Predicate<'db>>>, TypeError<DbInterner<'db>>> {
        let mut goals = Vec::new();

        self.insert_hidden_type(
            opaque_type_key.clone(),
            span,
            param_env.clone(),
            hidden_ty.clone(),
            &mut goals,
        )?;

        self.add_item_bounds_for_hidden_type(
            opaque_type_key.def_id,
            opaque_type_key.args,
            param_env,
            hidden_ty,
            &mut goals,
        );

        Ok(goals)
    }

    /// Insert a hidden type into the opaque type storage, making sure
    /// it hasn't previously been defined. This does not emit any
    /// constraints and it's the responsibility of the caller to make
    /// sure that the item bounds of the opaque are checked.
    pub fn inject_new_hidden_type_unchecked(
        &self,
        opaque_type_key: OpaqueTypeKey<'db>,
        hidden_ty: OpaqueHiddenType<'db>,
    ) {
        let prev = self.inner.borrow_mut().opaque_types().register(opaque_type_key, hidden_ty);
        assert_eq!(prev, None);
    }

    /// Insert a hidden type into the opaque type storage, equating it
    /// with any previous entries if necessary.
    ///
    /// This **does not** add the item bounds of the opaque as nested
    /// obligations. That is only necessary when normalizing the opaque
    /// itself, not when getting the opaque type constraints from
    /// somewhere else.
    pub fn insert_hidden_type(
        &self,
        opaque_type_key: OpaqueTypeKey<'db>,
        span: Span,
        param_env: ParamEnv<'db>,
        hidden_ty: Ty<'db>,
        goals: &mut Vec<Goal<'db, Predicate<'db>>>,
    ) -> Result<(), TypeError<DbInterner<'db>>> {
        // Ideally, we'd get the span where *this specific `ty` came
        // from*, but right now we just use the span from the overall
        // value being folded. In simple cases like `-> impl Foo`,
        // these are the same span, but not in cases like `-> (impl
        // Foo, impl Bar)`.
        match self.typing_mode() {
            TypingMode::Coherence => {
                // During intercrate we do not define opaque types but instead always
                // force ambiguity unless the hidden type is known to not implement
                // our trait.
                goals.push(Goal::new(self.interner, param_env, PredicateKind::Ambiguous));
            }
            TypingMode::Analysis { .. } => {
                let prev = self
                    .inner
                    .borrow_mut()
                    .opaque_types()
                    .register(opaque_type_key, OpaqueHiddenType { ty: hidden_ty.clone() });
                if let Some(prev) = prev {
                    goals.extend(
                        self.at(&ObligationCause::dummy_with_span(span), param_env)
                            .eq(DefineOpaqueTypes::Yes, prev, hidden_ty)?
                            .obligations
                            .into_iter()
                            // FIXME: Shuttling between obligations and goals is awkward.
                            .map(|value| Goal {
                                param_env: value.param_env.clone(),
                                predicate: value.predicate.clone(),
                            }),
                    );
                }
            }
            TypingMode::PostAnalysis => panic!("insert hidden type post-analysis"),
            TypingMode::Borrowck { defining_opaque_types } => todo!(),
            TypingMode::PostBorrowckAnalysis { defined_opaque_types } => todo!(),
        }

        Ok(())
    }

    pub fn add_item_bounds_for_hidden_type(
        &self,
        def_id: SolverDefId,
        args: GenericArgs<'db>,
        param_env: ParamEnv<'db>,
        hidden_ty: Ty<'db>,
        goals: &mut Vec<Goal<'db, Predicate<'db>>>,
    ) {
        // Require that the hidden type is well-formed. We have to
        // make sure we wf-check the hidden type to fix #114728.
        //
        // However, we don't check that all types are well-formed.
        // We only do so for types provided by the user or if they are
        // "used", e.g. for method selection.
        //
        // This means we never check the wf requirements of the hidden
        // type during MIR borrowck, causing us to infer the wrong
        // lifetime for its member constraints which then results in
        // unexpected region errors.
        goals.push(Goal::new(self.interner, param_env, ClauseKind::WellFormed(hidden_ty.into())));

        /*
        let replace_opaques_in = |clause: Clause, goals: &mut Vec<_>| {
            clause.fold_with(&mut BottomUpFolder {
                interner: DbInterner,
                ty_op: |ty| match ty.kind() {
                    // Replace all other mentions of the same opaque type with the hidden type,
                    // as the bounds must hold on the hidden type after all.
                    TyKind::Alias(AliasTyKind::Opaque, AliasTy { def_id: def_id2, args: args2, .. })
                        if def_id == def_id2 && args == args2 =>
                    {
                        hidden_ty
                    }
                    _ => ty,
                },
                lt_op: |lt| lt,
                ct_op: |ct| ct,
            })
        };

        let item_bounds = tcx.explicit_item_bounds(def_id);
        for (predicate, _) in item_bounds.iter_instantiated_copied(DbInterner, args) {
            let predicate = replace_opaques_in(predicate, goals);

            // Require that the predicate holds for the concrete type.
            debug!(?predicate);
            goals.push(Goal::new(DbInterner, param_env, predicate));
        }
        */

        /*
        // If this opaque is being defined and it's conditionally const,
        if self.tcx.is_conditionally_const(def_id) {
            let item_bounds = tcx.explicit_implied_const_bounds(def_id);
            for (predicate, _) in item_bounds.iter_instantiated_copied(tcx, args) {
                let predicate = replace_opaques_in(
                    predicate.to_host_effect_clause(self.tcx, BoundConstness::Maybe),
                    goals,
                );

                // Require that the predicate holds for the concrete type.
                debug!(?predicate);
                goals.push(Goal::new(self.tcx, param_env, predicate));
            }
        }
        */
    }
}
