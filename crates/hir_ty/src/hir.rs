#![allow(unused)]

use std::{iter::FromIterator, sync::Arc};

use hir_def::generics::TypeParamProvenance;
use hir_def::{
    db::DefDatabase, type_ref::Mutability, AdtId, GenericDefId, TraitId, TypeAliasId, TypeParamId,
};

use crate::{
    primitive::{FloatTy, IntTy},
    utils::make_mut_slice,
    OpaqueTyId,
};

// FIXME make this private once lowering only goes through queries
pub(super) mod lower;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum TypeName {
    /// The primitive boolean type. Written as `bool`.
    Bool,

    /// The primitive character type; holds a Unicode scalar value
    /// (a non-surrogate code point). Written as `char`.
    Char,

    /// A primitive integer type. For example, `i32`.
    Int(IntTy),

    /// A primitive floating-point type. For example, `f64`.
    Float(FloatTy),

    /// Structures, enumerations and unions.
    Adt(AdtId),

    /// The pointee of a string slice. Written as `str`.
    Str,

    /// The pointee of an array slice.  Written as `[T]`.
    Slice,

    /// An array with the given length. Written as `[T; n]`.
    Array,

    /// A raw pointer. Written as `*mut T` or `*const T`
    RawPtr(Mutability),

    /// A reference; a pointer with an associated lifetime. Written as
    /// `&'a mut T` or `&'a T`.
    Ref(Mutability),

    /// A pointer to a function.  Written as `fn() -> i32`.
    ///
    /// For example the type of `bar` here:
    ///
    /// ```
    /// fn foo() -> i32 { 1 }
    /// let bar: fn() -> i32 = foo;
    /// ```
    FnPtr { num_args: u16, is_varargs: bool },

    /// The never type `!`.
    Never,

    /// A tuple type.  For example, `(i32, bool)`.
    Tuple { cardinality: u16 },

    /// Represents a foreign type declared in external blocks.
    ForeignType(TypeAliasId),
}

/// A resolved type reference, as could be written somewhere in Rust code.
///
/// This is similar to `TypeRef`, but with all names resolved. So it does not
/// include unnameable types like type variables, closure types and similar.
///
/// This should be cheap to clone.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Type {
    /// A nominal type with (maybe 0) type parameters. This might be a primitive
    /// type like `bool`, a struct, tuple, function pointer, reference or
    /// several other things.
    Apply(ApplicationType),

    /// A "projection" type corresponds to an (unnormalized)
    /// projection like `<P0 as Trait<P1..Pn>>::Foo`. Note that the
    /// trait and all its parameters are fully known.
    Projection(ProjectionType),

    /// An opaque type (`impl Trait`).
    ///
    /// This is currently only used for return type impl trait; each instance of
    /// `impl Trait` in a return type gets its own ID.
    Opaque(OpaqueType),

    /// A type parameter; for example, `T` in `fn f<T>(x: T) {}`.
    // TODO rename to Param
    Placeholder(TypeParamId),

    /// A trait object (`dyn Trait` or bare `Trait` in pre-2018 Rust).
    Dyn(Arc<[Bound]>),

    /// A placeholder for types to be inferred (i.e. `_`).
    Infer,

    /// A placeholder for a type which could not be resolved; this is propagated
    /// to avoid useless error messages.
    Error,
}

/// A nominal type with (maybe 0) type arguments. This might be a primitive
/// type like `bool`, a struct, tuple, function pointer, reference or
/// several other things.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct ApplicationType {
    pub name: TypeName,
    pub arguments: TypeArgs,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct OpaqueType {
    pub opaque_ty_id: OpaqueTyId,
    pub arguments: TypeArgs,
}

/// A "projection" type corresponds to an (unnormalized)
/// projection like `<P0 as Trait<P1..Pn>>::Foo`. Note that the
/// trait and all its parameters are fully known.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct ProjectionType {
    pub associated_ty: TypeAliasId,
    // FIXME: instead provide self type and trait args separately?
    pub arguments: TypeArgs,
}

/// A list of substitutions for generic parameters.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct TypeArgs(Arc<[Type]>);

/// Like `generics::WherePredicate`, but with resolved types: A condition on the
/// parameters of a generic item. Unlike `GenericPredicate`, this does not
/// include the `Self` type of the bound.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Bound {
    /// The given trait needs to be implemented for its type parameters.
    Trait(TraitBound),
    /// An associated type bindings like in `Iterator<Item = T>`.
    AssocTypeBinding(AssocTypeBinding),
    /// We couldn't resolve the trait reference. (If some type parameters can't
    /// be resolved, they will just be `Error`).
    Error,
}

/// A trait with type parameters. This does not include the `Self`.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct TraitBound {
    pub trait_: TraitId,
    pub arguments: TypeArgs,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AssocTypeBinding {
    pub associated_ty: TypeAliasId,
    /// The arguments for the traits, without the Self type.
    pub arguments: TypeArgs,
    pub ty: Type,
}

impl Type {
    pub fn simple(name: TypeName) -> Self {
        Type::Apply(ApplicationType { name, arguments: TypeArgs::empty() })
    }
    pub fn apply_one(name: TypeName, arg: Type) -> Self {
        Type::Apply(ApplicationType { name, arguments: TypeArgs::single(arg) })
    }
    pub fn apply(name: TypeName, arguments: TypeArgs) -> Self {
        Type::Apply(ApplicationType { name, arguments })
    }
    pub fn unit() -> Self {
        Type::apply(TypeName::Tuple { cardinality: 0 }, TypeArgs::empty())
    }
}

impl TypeArgs {
    pub fn empty() -> Self {
        Self(Arc::new([]))
    }

    pub fn single(ty: Type) -> Self {
        Self(Arc::new([ty]))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn type_params_for_generics(generics: &crate::Generics) -> Self {
        generics
            .iter()
            .filter(|(_, data)| data.provenance != TypeParamProvenance::TraitSelf)
            .map(|(id, _)| Type::Placeholder(id))
            .collect()
    }

    pub fn type_params(db: &dyn DefDatabase, def: GenericDefId) -> Self {
        let generics = crate::generics(db, def);
        Self::type_params_for_generics(&generics)
    }
}

impl std::ops::Deref for TypeArgs {
    type Target = [Type];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl FromIterator<Type> for TypeArgs {
    fn from_iter<T: IntoIterator<Item = Type>>(iter: T) -> Self {
        TypeArgs(iter.into_iter().collect())
    }
}

impl Bound {
    pub fn is_error(&self) -> bool {
        matches!(self, Bound::Error)
    }
}

pub(crate) trait HirTypeWalk {
    fn walk(&self, f: &mut impl FnMut(&Type));
    fn walk_mut(&mut self, f: &mut impl FnMut(&mut Type));
}

impl HirTypeWalk for Type {
    fn walk(&self, f: &mut impl FnMut(&Type)) {
        match self {
            Type::Apply(a_ty) => {
                a_ty.arguments.walk(f);
            }
            Type::Projection(p_ty) => {
                p_ty.arguments.walk(f);
            }
            Type::Opaque(o_ty) => {
                o_ty.arguments.walk(f);
            }
            Type::Dyn(bounds) => {
                for bound in bounds.iter() {
                    bound.walk(f);
                }
            }
            Type::Placeholder(_) => {}
            Type::Infer => {}
            Type::Error => {}
        }
        f(self);
    }
    fn walk_mut(&mut self, f: &mut impl FnMut(&mut Type)) {
        match self {
            Type::Apply(a_ty) => {
                a_ty.arguments.walk_mut(f);
            }
            Type::Projection(p_ty) => {
                p_ty.arguments.walk_mut(f);
            }
            Type::Opaque(o_ty) => {
                o_ty.arguments.walk_mut(f);
            }
            Type::Dyn(bounds) => {
                for bound in make_mut_slice(bounds) {
                    bound.walk_mut(f);
                }
            }
            Type::Placeholder(_) => {}
            Type::Infer => {}
            Type::Error => {}
        }
        f(self);
    }
}
impl HirTypeWalk for TypeArgs {
    fn walk(&self, f: &mut impl FnMut(&Type)) {
        for t in self.0.iter() {
            t.walk(f);
        }
    }
    fn walk_mut(&mut self, f: &mut impl FnMut(&mut Type)) {
        for t in make_mut_slice(&mut self.0) {
            t.walk_mut(f);
        }
    }
}
impl HirTypeWalk for Bound {
    fn walk(&self, f: &mut impl FnMut(&Type)) {
        match self {
            Bound::Trait(tr) => {
                tr.walk(f);
            }
            Bound::AssocTypeBinding(b) => {
                b.walk(f);
            }
            Bound::Error => {}
        }
    }
    fn walk_mut(&mut self, f: &mut impl FnMut(&mut Type)) {
        match self {
            Bound::Trait(tr) => {
                tr.walk_mut(f);
            }
            Bound::AssocTypeBinding(b) => {
                b.walk_mut(f);
            }
            Bound::Error => {}
        }
    }
}
impl HirTypeWalk for TraitBound {
    fn walk(&self, f: &mut impl FnMut(&Type)) {
        self.arguments.walk(f);
    }
    fn walk_mut(&mut self, f: &mut impl FnMut(&mut Type)) {
        self.arguments.walk_mut(f);
    }
}
impl HirTypeWalk for AssocTypeBinding {
    fn walk(&self, f: &mut impl FnMut(&Type)) {
        self.ty.walk(f);
        self.arguments.walk(f);
    }
    fn walk_mut(&mut self, f: &mut impl FnMut(&mut Type)) {
        self.ty.walk_mut(f);
        self.arguments.walk_mut(f);
    }
}

pub(crate) fn substitute<T: HirTypeWalk + std::fmt::Debug>(
    generics: &crate::Generics,
    mut t: T,
    args: TypeArgs,
) -> T {
    // self params are skipped in the HIR
    let (_, self_params, _, _) = generics.provenance_split();
    t.walk_mut(&mut |ty| match ty {
        Type::Placeholder(param_id) => {
            if let Some(idx) = generics.param_idx(*param_id) {
                *ty = args[idx - self_params].clone();
            }
        }
        _ => {}
    });
    t
}

/// A function signature as seen by type inference: Several parameter types and
/// one return type.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FnSig {
    params_and_return: Arc<[Type]>,
    is_varargs: bool,
}

impl FnSig {
    pub fn from_params_and_return(mut params: Vec<Type>, ret: Type, is_varargs: bool) -> FnSig {
        params.push(ret);
        FnSig { params_and_return: params.into(), is_varargs }
    }

    pub fn from_fn_ptr_args(args: &TypeArgs, is_varargs: bool) -> FnSig {
        FnSig { params_and_return: Arc::clone(&args.0), is_varargs }
    }

    pub fn params(&self) -> &[Type] {
        &self.params_and_return[0..self.params_and_return.len() - 1]
    }

    pub fn ret(&self) -> &Type {
        &self.params_and_return[self.params_and_return.len() - 1]
    }
}

pub(crate) use lower::{
    const_type_query, function_signature_query, generic_bounds_for_param_query,
    generic_bounds_for_param_recover, generic_defaults_query, impl_self_type_query,
    impl_self_type_recover, impl_trait_query, static_type_query, type_alias_type_query,
    type_alias_type_recover,
};
