use crate::{
    hir::{AssocTypeBinding, Bound, TraitBound, Type, TypeArgs, TypeName},
    utils::generics,
    ApplicationTy, GenericPredicate, OpaqueTy, ProjectionPredicate, ProjectionTy, Substs, TraitRef,
    Ty, TypeCtor,
};

use super::InferenceContext;
use chalk_ir::{BoundVar, DebruijnIndex};

pub(super) struct InstantiateContext<'a, 'b> {
    inf_ctx: &'b mut InferenceContext<'a>,
    impl_trait_mode: ImplTraitInstantiationMode,
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

impl<'a> InferenceContext<'a> {
    pub(super) fn instantiate_ctx(&mut self) -> InstantiateContext<'a, '_> {
        InstantiateContext { inf_ctx: self, impl_trait_mode: ImplTraitInstantiationMode::Opaque }
    }
}

impl<'a, 'b> InstantiateContext<'a, 'b> {
    pub(super) fn with_impl_trait_as_variables(self) -> Self {
        InstantiateContext { impl_trait_mode: ImplTraitInstantiationMode::Variable, ..self }
    }

    pub(super) fn instantiate_type(&mut self, typ: &Type) -> Ty {
        match typ {
            Type::Apply(apply_ty) => Ty::Apply(ApplicationTy {
                ctor: instantiate_ctor(apply_ty.name),
                parameters: self.instantiate_args(&apply_ty.arguments),
            }),
            Type::Projection(proj_ty) => {
                debug_assert!(
                    {
                        let generics =
                            generics(self.inf_ctx.db.upcast(), proj_ty.associated_ty.into());
                        generics.len() == proj_ty.arguments.len()
                    },
                    "proj_ty: {:?}",
                    proj_ty
                );
                let projection_ty = ProjectionTy {
                    associated_ty: proj_ty.associated_ty,
                    parameters: self.instantiate_args(&proj_ty.arguments),
                };
                self.inf_ctx.normalize_projection_ty(projection_ty)
            }
            Type::Opaque(opaque_ty) => match self.impl_trait_mode {
                ImplTraitInstantiationMode::Opaque => Ty::Opaque(OpaqueTy {
                    opaque_ty_id: opaque_ty.opaque_ty_id,
                    parameters: self.instantiate_args(&opaque_ty.arguments),
                }),
                ImplTraitInstantiationMode::Variable => {
                    let var = self.inf_ctx.table.new_type_var();
                    // TODO obligations
                    var
                }
            },
            Type::Placeholder(param_id) => Ty::Placeholder(*param_id),
            Type::Dyn(bounds) => {
                let self_ty = Ty::Bound(BoundVar::new(DebruijnIndex::INNERMOST, 0));
                Ty::Dyn(bounds.iter().map(|b| self.instantiate_bound(b, self_ty.clone())).collect())
            }
            Type::Infer => self.inf_ctx.table.new_type_var(),
            Type::Error => Ty::Unknown,
        }
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

    fn instantiate_trait_bound(&mut self, trait_bound: &TraitBound, self_ty: Ty) -> TraitRef {
        let substs = Substs::build_for_def(self.inf_ctx.db, trait_bound.trait_)
            .push(self_ty)
            .fill_exact(trait_bound.arguments.iter().map(|typ| self.instantiate_type(typ)))
            .build();
        TraitRef { trait_: trait_bound.trait_, substs }
    }

    fn instantiate_assoc_type_binding(
        &mut self,
        assoc_type_binding: &AssocTypeBinding,
        self_ty: Ty,
    ) -> ProjectionPredicate {
        let substs = Substs::build_for_def(self.inf_ctx.db, assoc_type_binding.associated_ty)
            .push(self_ty)
            .fill_exact(assoc_type_binding.arguments.iter().map(|typ| self.instantiate_type(typ)))
            .build();
        let projection_ty =
            ProjectionTy { associated_ty: assoc_type_binding.associated_ty, parameters: substs };
        let ty = self.instantiate_type(&assoc_type_binding.ty);
        ProjectionPredicate { projection_ty, ty }
    }

    fn instantiate_args(&mut self, args: &TypeArgs) -> Substs {
        Substs(args.iter().map(|typ| self.instantiate_type(typ)).collect())
    }
}

fn instantiate_ctor(name: TypeName) -> TypeCtor {
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
    }
}
