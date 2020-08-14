
use crate::{Ty, hir::{TypeArgs, Type, TypeName}, Substs, ApplicationTy, ProjectionTy, TypeCtor};

use super::InferenceContext;

impl<'a> InferenceContext<'a> {
    pub(super) fn instantiate_type(&mut self, typ: &Type) -> Ty {
        match typ {
            Type::Apply(apply_ty) => {
                Ty::Apply(ApplicationTy {
                    ctor: instantiate_ctor(apply_ty.name),
                    parameters: self.instantiate_args(&apply_ty.arguments),
                })
            }
            Type::Projection(proj_ty) => {
                Ty::Projection(ProjectionTy {
                    associated_ty: proj_ty.associated_ty,
                    parameters: self.instantiate_args(&proj_ty.arguments),
                })
            }
            Type::Opaque(_) => todo!(),
            Type::Placeholder(param_id) => Ty::Placeholder(*param_id),
            Type::Dyn(_) => todo!(),
            Type::Infer => self.table.new_type_var(),
            Type::Error => Ty::Unknown,
        }
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
