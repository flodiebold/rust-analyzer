/// Instantiation is the process of going from a `hir_ty::hir::Type` to a `Ty`,
/// which is the representation used for type inference. This may involve
/// creating inference variables and trait obligations to be checked later, so
/// it's not a simple transformation, but something that modifies the
/// surrounding context.
use crate::{
    db::HirDatabase,
    hir::{AssocTypeBinding, Bound, TraitBound, Type, TypeArgs, TypeName, WhereClause},
    utils::generics,
    ApplicationTy, Binders, GenericPredicate, Obligation, OpaqueTy, ProjectionPredicate,
    ProjectionTy, Substs, TraitRef, Ty, TypeCtor, TypeWalk, ValueTyDefId,
};

use super::InferenceContext;
use chalk_ir::{BoundVar, DebruijnIndex};
use hir_def::{adt::StructKind, EnumVariantId, GenericDefId, StructId};
use stdx::never;

trait InstantiateOps {
    fn new_type_var(&mut self) -> Ty;
    fn push_obligation(&mut self, obligation: Obligation);

    fn normalize_projection_ty(&mut self, proj_ty: ProjectionTy) -> Ty {
        let var = self.new_type_var();
        let predicate = ProjectionPredicate { projection_ty: proj_ty, ty: var.clone() };
        let obligation = Obligation::Projection(predicate);
        self.push_obligation(obligation);
        var
    }
}

pub(crate) struct InstantiateContext<'a, 'b> {
    db: &'a dyn HirDatabase,
    inf_ctx: &'b mut (dyn InstantiateOps + 'a),
    impl_trait_mode: ImplTraitInstantiationMode,
    type_param_mode: TypeParamInstantiationMode,
    shift: DebruijnIndex,
}

impl<'a> InstantiateOps for InferenceContext<'a> {
    fn new_type_var(&mut self) -> Ty {
        self.table.new_type_var()
    }

    fn push_obligation(&mut self, obligation: Obligation) {
        self.obligations.push(obligation);
    }
}

pub(crate) struct NoopInstantiateOps;
impl InstantiateOps for NoopInstantiateOps {
    fn new_type_var(&mut self) -> Ty {
        // FIXME: maybe assert, not sure
        Ty::Unknown
    }

    fn push_obligation(&mut self, _obligation: Obligation) {
        // FIXME: maybe assert, not sure
    }

    fn normalize_projection_ty(&mut self, proj_ty: ProjectionTy) -> Ty {
        Ty::Projection(proj_ty)
    }
}

impl NoopInstantiateOps {
    pub(crate) fn ctx_with_substs<'a>(
        &mut self,
        db: &'a dyn HirDatabase,
        def: GenericDefId,
        substs: Substs,
    ) -> InstantiateContext<'a, '_> {
        InstantiateContext {
            db,
            inf_ctx: self,
            impl_trait_mode: ImplTraitInstantiationMode::Opaque,
            type_param_mode: TypeParamInstantiationMode::Substitute(def, substs),
            shift: DebruijnIndex::INNERMOST,
        }
    }

    pub(crate) fn ctx_local<'a>(
        &mut self,
        db: &'a dyn HirDatabase,
        def: Option<GenericDefId>,
    ) -> InstantiateContext<'a, '_> {
        InstantiateContext {
            db,
            inf_ctx: self,
            impl_trait_mode: ImplTraitInstantiationMode::Opaque,
            type_param_mode: def.map_or(TypeParamInstantiationMode::Forbidden, TypeParamInstantiationMode::Local),
            shift: DebruijnIndex::INNERMOST,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ImplTraitInstantiationMode {
    /// `impl Trait` gets instantiated as an opaque type. Used for return position
    /// impl Trait outside the function.
    Opaque,
    /// `impl Trait` gets lowered into a type variable and obligations. Used for
    /// return position impl trait inside the function.
    Variable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeParamInstantiationMode {
    /// There should be no type parameters.
    Forbidden,
    /// The type we're instantiating is written in the scope of the given
    /// definition, and we're instantiating it in that scope, so we're checking
    /// that type parameters belong to that definition and then instantiating
    /// them as placeholders.
    Local(GenericDefId),
    /// The type we're instantiating is written in the scope of the given
    /// definition, and we're instantiating it in a different scope, so we're
    /// checking that type parameters belong to that definition and then
    /// substituting them by different types.
    Substitute(GenericDefId, Substs),
}

impl<'a> InferenceContext<'a> {
    pub(super) fn instantiate_ctx_no_substs(&mut self) -> InstantiateContext<'a, '_> {
        InstantiateContext {
            db: self.db,
            inf_ctx: self,
            impl_trait_mode: ImplTraitInstantiationMode::Opaque,
            type_param_mode: TypeParamInstantiationMode::Forbidden,
            shift: DebruijnIndex::INNERMOST,
        }
    }

    pub(super) fn instantiate_ctx_local(&mut self) -> InstantiateContext<'a, '_> {
        let type_param_mode = self
            .resolver
            .generic_def()
            .map_or(TypeParamInstantiationMode::Forbidden, TypeParamInstantiationMode::Local);
        InstantiateContext {
            db: self.db,
            inf_ctx: self,
            impl_trait_mode: ImplTraitInstantiationMode::Opaque,
            type_param_mode,
            shift: DebruijnIndex::INNERMOST,
        }
    }

    pub(super) fn instantiate_ctx_with_substs(
        &mut self,
        def: GenericDefId,
        substs: Substs,
    ) -> InstantiateContext<'a, '_> {
        InstantiateContext {
            db: self.db,
            inf_ctx: self,
            impl_trait_mode: ImplTraitInstantiationMode::Opaque,
            type_param_mode: TypeParamInstantiationMode::Substitute(def, substs),
            shift: DebruijnIndex::INNERMOST,
        }
    }

    pub(super) fn instantiate_ty_for_struct_constructor(
        &mut self,
        def: StructId,
        substs: Substs,
    ) -> Ty {
        let struct_data = self.db.struct_data(def);
        if let StructKind::Unit = struct_data.variant_data.kind() {
            return Ty::apply(TypeCtor::Adt(def.into()), substs);
        }
        Ty::apply(TypeCtor::FnDef(def.into()), substs)
    }

    pub(super) fn instantiate_ty_for_value(&mut self, def: ValueTyDefId, substs: Substs) -> Ty {
        match def {
            ValueTyDefId::FunctionId(it) => Ty::apply(TypeCtor::FnDef(it.into()), substs),
            ValueTyDefId::StructId(it) => self.instantiate_ty_for_struct_constructor(it, substs),
            ValueTyDefId::UnionId(it) => Ty::apply(TypeCtor::Adt(it.into()), substs),
            ValueTyDefId::EnumVariantId(it) => {
                self.instantiate_ty_for_enum_variant_constructor(it, substs)
            }
            ValueTyDefId::ConstId(it) => {
                let typ = self.db.const_type(it);
                self.instantiate_ctx_with_substs(it.into(), substs).instantiate(&typ)
            }
            ValueTyDefId::StaticId(it) => {
                never!(!substs.is_empty());
                let typ = self.db.static_type(it);
                self.instantiate_ctx_no_substs().instantiate(&typ)
            }
        }
    }

    fn instantiate_ty_for_enum_variant_constructor(
        &mut self,
        def: EnumVariantId,
        substs: Substs,
    ) -> Ty {
        let enum_data = self.db.enum_data(def.parent);
        let var_data = &enum_data.variants[def.local_id].variant_data;
        if let StructKind::Unit = var_data.kind() {
            return Ty::apply(TypeCtor::Adt(def.parent.into()), substs);
        }
        Ty::apply(TypeCtor::FnDef(def.into()), substs)
    }
}

pub(crate) trait Instantiate {
    type InstantiatedType: std::fmt::Debug;
    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType;
}

impl<'a, 'b> InstantiateContext<'a, 'b> {
    pub(crate) fn with_impl_trait_as_variables(self) -> Self {
        InstantiateContext { impl_trait_mode: ImplTraitInstantiationMode::Variable, ..self }
    }

    pub fn instantiate<T: Instantiate>(&mut self, t: &T) -> T::InstantiatedType {
        t.do_instantiate(self)
    }

    fn instantiate_bound(&mut self, bound: &Bound, self_ty: Ty) -> GenericPredicate {
        match bound {
            Bound::Trait(trait_bound) => {
                GenericPredicate::Implemented(self.instantiate_trait_bound(trait_bound, self_ty))
            }
            Bound::AssocTypeBinding(assoc_type_binding) => GenericPredicate::Projection(
                self.instantiate_assoc_type_binding(assoc_type_binding, self_ty),
            ),
            Bound::Error => GenericPredicate::Error,
        }
    }

    pub fn instantiate_trait_bound(&mut self, trait_bound: &TraitBound, self_ty: Ty) -> TraitRef {
        let substs = Substs::build_for_def(self.db, trait_bound.trait_)
            .push(self_ty)
            .fill_exact(trait_bound.arguments.iter().map(|typ| self.instantiate(typ)))
            .build();
        TraitRef { trait_: trait_bound.trait_, substs }
    }

    fn instantiate_assoc_type_binding(
        &mut self,
        assoc_type_binding: &AssocTypeBinding,
        self_ty: Ty,
    ) -> ProjectionPredicate {
        let substs = Substs::build_for_def(self.db, assoc_type_binding.associated_ty)
            .push(self_ty)
            .fill_exact(assoc_type_binding.arguments.iter().map(|typ| self.instantiate(typ)))
            .build();
        let projection_ty =
            ProjectionTy { associated_ty: assoc_type_binding.associated_ty, parameters: substs };
        let ty = self.instantiate(&assoc_type_binding.ty);
        ProjectionPredicate { projection_ty, ty }
    }

    fn normalize_projection_ty(&mut self, proj_ty: ProjectionTy) -> Ty {
        self.inf_ctx.normalize_projection_ty(proj_ty)
    }
}

impl Instantiate for Type {
    type InstantiatedType = Ty;

    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType {
        match self {
            Type::Apply(apply_ty) => Ty::Apply(ApplicationTy {
                ctor: instantiate_ctor(apply_ty.name),
                parameters: ctx.instantiate(&apply_ty.arguments),
            }),
            Type::Projection(proj_ty) => {
                debug_assert!(
                    {
                        let generics = generics(ctx.db.upcast(), proj_ty.associated_ty.into());
                        generics.len() == proj_ty.arguments.len()
                    },
                    "proj_ty: {:?}",
                    proj_ty
                );
                let projection_ty = ProjectionTy {
                    associated_ty: proj_ty.associated_ty,
                    parameters: ctx.instantiate(&proj_ty.arguments),
                };
                ctx.normalize_projection_ty(projection_ty)
            }
            Type::Opaque(opaque_ty) => match ctx.impl_trait_mode {
                ImplTraitInstantiationMode::Opaque => Ty::Opaque(OpaqueTy {
                    opaque_ty_id: opaque_ty.opaque_ty_id,
                    parameters: ctx.instantiate(&opaque_ty.arguments),
                }),
                ImplTraitInstantiationMode::Variable => {
                    let var = ctx.inf_ctx.new_type_var();
                    // TODO obligations
                    var
                }
            },
            Type::Param(param_id) => match &ctx.type_param_mode {
                TypeParamInstantiationMode::Forbidden => {
                    never!(true);
                    Ty::Unknown
                }
                TypeParamInstantiationMode::Local(def) => {
                    let generics = generics(ctx.db.upcast(), *def);
                    if never!(generics.param_idx(*param_id).is_none()) {
                        Ty::Unknown
                    } else {
                        Ty::Placeholder(*param_id)
                    }
                }
                TypeParamInstantiationMode::Substitute(def, substs) => {
                    let generics = generics(ctx.db.upcast(), *def);
                    let idx = if let Some(idx) = generics.param_idx(*param_id) {
                        idx
                    } else {
                        never!(true);
                        return Ty::Unknown;
                    };
                    substs[idx].clone().shift_bound_vars(ctx.shift)
                }
            },
            Type::Dyn(bounds) => {
                let self_ty = Ty::Bound(BoundVar::new(DebruijnIndex::INNERMOST, 0));
                ctx.shift.shift_in();
                let result = Ty::Dyn(
                    bounds.iter().map(|b| ctx.instantiate_bound(b, self_ty.clone())).collect(),
                );
                ctx.shift.shift_out();
                result
            }
            Type::Infer => ctx.inf_ctx.new_type_var(),
            Type::Error => Ty::Unknown,
        }
    }
}

impl Instantiate for TypeArgs {
    type InstantiatedType = Substs;

    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType {
        Substs(self.iter().map(|typ| ctx.instantiate(typ)).collect())
    }
}

impl Instantiate for Bound {
    type InstantiatedType = Binders<GenericPredicate>;

    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType {
        ctx.shift.shift_in();
        let inner =
            ctx.instantiate_bound(self, Ty::Bound(BoundVar::new(DebruijnIndex::INNERMOST, 0)));
        ctx.shift.shift_out();
        Binders::new(1, inner)
    }
}

impl Instantiate for crate::hir::FnSig {
    type InstantiatedType = crate::FnSig;

    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType {
        crate::FnSig::from_params_and_return(
            self.params().iter().map(|t| ctx.instantiate(t)).collect(),
            ctx.instantiate(self.ret()),
            self.is_varargs,
        )
    }
}

impl Instantiate for TraitBound {
    type InstantiatedType = Binders<TraitRef>;

    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType {
        ctx.shift.shift_in();
        let trait_ref = ctx
            .instantiate_trait_bound(self, Ty::Bound(BoundVar::new(DebruijnIndex::INNERMOST, 0)));
        ctx.shift.shift_out();
        Binders::new(1, trait_ref)
    }
}

impl Instantiate for WhereClause {
    type InstantiatedType = GenericPredicate;

    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType {
        let self_ty = ctx.instantiate(&self.ty);
        ctx.instantiate_bound(&self.bound, self_ty)
    }
}

impl<T: Instantiate> Instantiate for &[T] {
    type InstantiatedType = Vec<T::InstantiatedType>;

    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType {
        self.iter().map(|t| ctx.instantiate(t)).collect()
    }
}

impl<T: Instantiate, U: Instantiate> Instantiate for (T, U) {
    type InstantiatedType = (T::InstantiatedType, U::InstantiatedType);

    fn do_instantiate<'a, 'b>(
        &self,
        ctx: &mut InstantiateContext<'a, 'b>,
    ) -> Self::InstantiatedType {
        (ctx.instantiate(&self.0), ctx.instantiate(&self.1))
    }
}

pub(crate) fn instantiate_ctor(name: TypeName) -> TypeCtor {
    match name {
        TypeName::Bool => TypeCtor::Bool,
        TypeName::Char => TypeCtor::Char,
        TypeName::Int(int_ty) => TypeCtor::Int(int_ty),
        TypeName::Float(float_ty) => TypeCtor::Float(float_ty),
        TypeName::Adt(adt) => TypeCtor::Adt(adt),
        TypeName::Str => TypeCtor::Str,
        TypeName::Slice => TypeCtor::Slice,
        TypeName::Array => TypeCtor::Array,
        TypeName::RawPtr(m) => TypeCtor::RawPtr(m),
        TypeName::Ref(m) => TypeCtor::Ref(m),
        TypeName::FnPtr { num_args, is_varargs } => TypeCtor::FnPtr { num_args, is_varargs },
        TypeName::Never => TypeCtor::Never,
        TypeName::Tuple { cardinality } => TypeCtor::Tuple { cardinality },
        TypeName::ForeignType(t) => TypeCtor::ForeignType(t),
    }
}

pub(crate) fn instantiate_outside_inference<T: Instantiate>(
    db: &dyn HirDatabase,
    def: GenericDefId,
    t: &T,
) -> Binders<T::InstantiatedType> {
    let generics = generics(db.upcast(), def);
    let substs = Substs::bound_vars(&generics, DebruijnIndex::INNERMOST);
    let instantiated = NoopInstantiateOps.ctx_with_substs(db, def, substs).instantiate(t);
    Binders::new(generics.len(), instantiated)
}

pub(crate) fn instantiate_outside_inference_local<T: Instantiate>(
    db: &dyn HirDatabase,
    def: Option<GenericDefId>,
    t: &T,
) -> T::InstantiatedType {
    NoopInstantiateOps.ctx_local(db, def).instantiate(t)
}
