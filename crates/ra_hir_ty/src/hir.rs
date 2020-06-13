#![allow(unused)]

use std::{iter::FromIterator, sync::Arc};

use hir_def::{
    db::DefDatabase, type_ref::Mutability, AdtId, GenericDefId, TraitId, TypeAliasId, TypeParamId,
};

use crate::{
    primitive::{FloatTy, IntTy},
    OpaqueTyId,
};

mod lower;

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

    /// A placeholder for a type parameter; for example, `T` in `fn f<T>(x: T)
    /// {}` when we're type-checking the body of that function. In this
    /// situation, we know this stands for *some* type, but don't know the exact
    /// type.
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
        generics.iter().map(|(id, _)| Type::Placeholder(id)).collect()
    }

    pub fn type_params(db: &dyn DefDatabase, def: GenericDefId) -> Self {
        let generics = crate::generics(db, def);
        Self::type_params_for_generics(&generics)
    }
}

impl FromIterator<Type> for TypeArgs {
    fn from_iter<T: IntoIterator<Item = Type>>(iter: T) -> Self {
        TypeArgs(iter.into_iter().collect())
    }
}

pub(crate) trait HirTypeWalk {}

impl HirTypeWalk for Type {}
impl HirTypeWalk for TypeArgs {}
impl HirTypeWalk for Bound {}
impl HirTypeWalk for TraitBound {}

pub(crate) fn substitute<T: HirTypeWalk>(generics: &crate::Generics, t: T, args: TypeArgs) -> T {
    todo!()
}

pub(crate) use lower::{
    generic_bounds_for_param_query, generic_bounds_for_param_recover, generic_defaults_query,
    impl_self_ty_query, impl_self_ty_recover, impl_trait_query, type_alias_type_query,
    type_alias_type_recover,
};
