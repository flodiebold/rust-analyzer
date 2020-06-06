use std::sync::Arc;

use hir_def::{type_ref::Mutability, AdtId, TypeAliasId, TypeParamId, TraitId};

use crate::{primitive::{FloatTy, IntTy}, OpaqueTyId};

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
    FnPtr { num_args: u16 },

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

    /// A bound type variable. This is used in various places: when representing
    /// some polymorphic type like the type of function `fn f<T>`, the type
    /// parameters get turned into variables; during trait resolution, inference
    /// variables get turned into bound variables and back; and in `Dyn` the
    /// `Self` type is represented with a bound variable as well.
    // Bound(BoundVar), // TODO maybe not necessary

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
