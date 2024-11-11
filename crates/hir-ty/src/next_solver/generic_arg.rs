use rustc_type_ir::{
    fold::TypeFoldable,
    inherent::{GenericArg as _, GenericsOf, IntoKind, SliceLike},
    relate::Relate,
    visit::TypeVisitable,
    GenericArgKind, Interner, TermKind, TyKind,
};
use smallvec::SmallVec;

use super::{
    generics::GenericParamDef, with_db_out_of_thin_air, Const, DbInterner, DefId, Generics, Region,
    Ty,
};

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

interned_vec!(GenericArgs, GenericArg, slice);

impl From<Ty> for GenericArg {
    fn from(value: Ty) -> Self {
        Self::Ty(value)
    }
}

impl From<Region> for GenericArg {
    fn from(value: Region) -> Self {
        Self::Lifetime(value)
    }
}

impl From<Const> for GenericArg {
    fn from(value: Const) -> Self {
        Self::Const(value)
    }
}

impl IntoKind for GenericArg {
    type Kind = GenericArgKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        match self {
            GenericArg::Ty(ty) => GenericArgKind::Type(ty),
            GenericArg::Lifetime(region) => GenericArgKind::Lifetime(region),
            GenericArg::Const(c) => GenericArgKind::Const(c),
        }
    }
}

impl TypeVisitable<DbInterner> for GenericArg {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        match self {
            GenericArg::Lifetime(lt) => lt.visit_with(visitor),
            GenericArg::Ty(ty) => ty.visit_with(visitor),
            GenericArg::Const(ct) => ct.visit_with(visitor),
        }
    }
}

impl TypeFoldable<DbInterner> for GenericArg {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        match self.kind() {
            GenericArgKind::Lifetime(lt) => lt.try_fold_with(folder).map(Into::into),
            GenericArgKind::Type(ty) => ty.try_fold_with(folder).map(Into::into),
            GenericArgKind::Const(ct) => ct.try_fold_with(folder).map(Into::into),
        }
    }
}

impl Relate<DbInterner> for GenericArg {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        match (a.kind(), b.kind()) {
            (GenericArgKind::Lifetime(a_lt), GenericArgKind::Lifetime(b_lt)) => {
                Ok(relation.relate(a_lt, b_lt)?.into())
            }
            (GenericArgKind::Type(a_ty), GenericArgKind::Type(b_ty)) => {
                Ok(relation.relate(a_ty, b_ty)?.into())
            }
            (GenericArgKind::Const(a_ct), GenericArgKind::Const(b_ct)) => {
                Ok(relation.relate(a_ct, b_ct)?.into())
            }
            (GenericArgKind::Lifetime(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
            (GenericArgKind::Type(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
            (GenericArgKind::Const(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
        }
    }
}

impl rustc_type_ir::inherent::GenericArg<DbInterner> for GenericArg {}

impl GenericArgs {
    /// Creates an `GenericArgs` for generic parameter definitions,
    /// by calling closures to obtain each kind.
    /// The closures get to observe the `GenericArgs` as they're
    /// being built, which can be used to correctly
    /// replace defaults of generic parameters.
    pub fn for_item<F>(interner: DbInterner, def_id: DefId, mut mk_kind: F) -> GenericArgs
    where
        F: FnMut(&GenericParamDef, &[GenericArg]) -> GenericArg,
    {
        let defs = interner.generics_of(def_id);
        let count = defs.count();
        let mut args = SmallVec::with_capacity(count);
        Self::fill_item(&mut args, interner, defs, &mut mk_kind);
        interner.mk_args(&args)
    }

    pub fn fill_item<F>(
        args: &mut SmallVec<[GenericArg; 8]>,
        interner: DbInterner,
        defs: Generics,
        mk_kind: &mut F,
    ) where
        F: FnMut(&GenericParamDef, &[GenericArg]) -> GenericArg,
    {
        if let Some(def_id) = defs.parent {
            let parent_defs = interner.generics_of(def_id);
            Self::fill_item(args, interner, parent_defs, mk_kind);
        }
        Self::fill_single(args, defs, mk_kind);
    }

    pub fn fill_single<F>(args: &mut SmallVec<[GenericArg; 8]>, defs: Generics, mk_kind: &mut F)
    where
        F: FnMut(&GenericParamDef, &[GenericArg]) -> GenericArg,
    {
        args.reserve(defs.own_params.len());
        for param in &defs.own_params {
            let kind = mk_kind(param, args);
            assert_eq!(param.index as usize, args.len(), "{args:#?}, {defs:#?}");
            args.push(kind);
        }
    }
}

impl rustc_type_ir::inherent::GenericArgs<DbInterner> for GenericArgs {
    fn rebase_onto(
        self,
        interner: DbInterner,
        source_def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        target: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> <DbInterner as rustc_type_ir::Interner>::GenericArgs {
        let defs = interner.generics_of(source_def_id);
        interner.mk_args_from_iter(target.iter().chain(self.iter().skip(defs.count())))
    }

    fn type_at(self, i: usize) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        with_db_out_of_thin_air(|db| {
            db.lookup_intern_rustc_generic_args(self)
                .0
                .get(i)
                .and_then(|g| g.as_type())
                .unwrap_or(Ty::error())
        })
    }

    fn region_at(self, i: usize) -> <DbInterner as rustc_type_ir::Interner>::Region {
        with_db_out_of_thin_air(|db| {
            db.lookup_intern_rustc_generic_args(self)
                .0
                .get(i)
                .and_then(|g| g.as_region())
                .unwrap_or(Region::error())
        })
    }

    fn const_at(self, i: usize) -> <DbInterner as rustc_type_ir::Interner>::Const {
        with_db_out_of_thin_air(|db| {
            db.lookup_intern_rustc_generic_args(self)
                .0
                .get(i)
                .and_then(|g| g.as_const())
                .unwrap_or(Const::error())
        })
    }

    fn identity_for_item(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
    ) -> <DbInterner as rustc_type_ir::Interner>::GenericArgs {
        Self::for_item(interner, def_id.into(), |param, _| interner.mk_param_from_def(param))
    }

    fn extend_with_error(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        original_args: &[<DbInterner as rustc_type_ir::Interner>::GenericArg],
    ) -> <DbInterner as rustc_type_ir::Interner>::GenericArgs {
        Self::for_item(interner, def_id.into(), |def, _| {
            if let Some(arg) = original_args.get(def.index as usize) {
                *arg
            } else {
                def.to_error(interner)
            }
        })
    }

    fn split_closure_args(self) -> rustc_type_ir::ClosureArgsParts<DbInterner> {
        with_db_out_of_thin_air(|db| {
            match db.lookup_intern_rustc_generic_args(self)[..] {
                [ref parent_args @ .., closure_kind_ty, closure_sig_as_fn_ptr_ty, tupled_upvars_ty] => {
                    rustc_type_ir::ClosureArgsParts {
                        parent_args: GenericArgsSlice(self, 0, parent_args.len()),
                        closure_kind_ty: closure_kind_ty.expect_ty(),
                        closure_sig_as_fn_ptr_ty: closure_sig_as_fn_ptr_ty.expect_ty(),
                        tupled_upvars_ty: tupled_upvars_ty.expect_ty(),
                    }
                }
                _ => todo!(), // rustc has `bug!` here?, should we have error report
            }
        })
    }

    fn split_coroutine_closure_args(self) -> rustc_type_ir::CoroutineClosureArgsParts<DbInterner> {
        with_db_out_of_thin_air(|db| match db.lookup_intern_rustc_generic_args(self)[..] {
            [ref parent_args @ .., closure_kind_ty, signature_parts_ty, tupled_upvars_ty, coroutine_captures_by_ref_ty, coroutine_witness_ty] => {
                rustc_type_ir::CoroutineClosureArgsParts {
                    parent_args: GenericArgsSlice(self, 0, parent_args.len()),
                    closure_kind_ty: closure_kind_ty.expect_ty(),
                    signature_parts_ty: signature_parts_ty.expect_ty(),
                    tupled_upvars_ty: tupled_upvars_ty.expect_ty(),
                    coroutine_captures_by_ref_ty: coroutine_captures_by_ref_ty.expect_ty(),
                    coroutine_witness_ty: coroutine_witness_ty.expect_ty(),
                }
            }
            _ => todo!(), // rustc has `bug!` here?, should we have error report
        })
    }

    fn split_coroutine_args(self) -> rustc_type_ir::CoroutineArgsParts<DbInterner> {
        with_db_out_of_thin_air(|db| {
            match db.lookup_intern_rustc_generic_args(self)[..] {
                [ref parent_args @ .., kind_ty, resume_ty, yield_ty, return_ty, witness, tupled_upvars_ty] => {
                    rustc_type_ir::CoroutineArgsParts {
                        parent_args: GenericArgsSlice(self, 0, parent_args.len()),
                        kind_ty: kind_ty.expect_ty(),
                        resume_ty: resume_ty.expect_ty(),
                        yield_ty: yield_ty.expect_ty(),
                        return_ty: return_ty.expect_ty(),
                        witness: witness.expect_ty(),
                        tupled_upvars_ty: tupled_upvars_ty.expect_ty(),
                    }
                }
                _ => todo!(), // rustc has `bug!` here?, should we have error report
            }
        })
    }
}

impl IntoKind for Term {
    type Kind = TermKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        match self {
            Term::Ty(ty) => TermKind::Ty(ty),
            Term::Const(c) => TermKind::Const(c),
        }
    }
}

impl From<Ty> for Term {
    fn from(value: Ty) -> Self {
        Self::Ty(value)
    }
}

impl From<Const> for Term {
    fn from(value: Const) -> Self {
        Self::Const(value)
    }
}

impl TypeVisitable<DbInterner> for Term {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        match self {
            Term::Ty(ty) => ty.visit_with(visitor),
            Term::Const(ct) => ct.visit_with(visitor),
        }
    }
}

impl TypeFoldable<DbInterner> for Term {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        match self.kind() {
            TermKind::Ty(ty) => ty.try_fold_with(folder).map(Into::into),
            TermKind::Const(ct) => ct.try_fold_with(folder).map(Into::into),
        }
    }
}

impl Relate<DbInterner> for Term {
    fn relate<R: rustc_type_ir::relate::TypeRelation<DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        match (a.kind(), b.kind()) {
            (TermKind::Ty(a_ty), TermKind::Ty(b_ty)) => Ok(relation.relate(a_ty, b_ty)?.into()),
            (TermKind::Const(a_ct), TermKind::Const(b_ct)) => {
                Ok(relation.relate(a_ct, b_ct)?.into())
            }
            (TermKind::Ty(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
            (TermKind::Const(unpacked), x) => {
                unreachable!("impossible case reached: can't relate: {:?} with {:?}", unpacked, x)
            }
        }
    }
}

impl rustc_type_ir::inherent::Term<DbInterner> for Term {}

impl DbInterner {
    pub(super) fn mk_args(self, args: &[GenericArg]) -> GenericArgs {
        self.with_db(|db| db.intern_rustc_generic_args(InternedGenericArgs(args.to_vec())))
    }

    pub(super) fn mk_args_from_iter<I, T>(self, iter: I) -> T::Output
    where
        I: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<GenericArg, GenericArgs>,
    {
        T::collect_and_apply(iter, |xs| self.mk_args(xs))
    }

    pub(super) fn check_args_compatible(self, def_id: DefId, args: GenericArgs) -> bool {
        // TODO
        true
    }

    pub(super) fn debug_assert_args_compatible(self, def_id: DefId, args: GenericArgs) {
        // TODO
    }
}
