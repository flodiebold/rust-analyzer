//! An iterator over the type substructure.
//! WARNING: this does not keep track of the region depth.

use rustc_hash::FxHashSet;
use rustc_type_ir::{
    GenericArgKind, TermKind,
    inherent::{ExprConst, IntoKind, SliceLike},
};
use smallvec::{SmallVec, smallvec};
use tracing::debug;

use super::{
    Const, ConstKind, DbInterner, ExistentialPredicate, GenericArg, GenericArgs, Ty, TyKind,
};

// The TypeWalker's stack is hot enough that it's worth going to some effort to
// avoid heap allocations.
type TypeWalkerStack<'db> = SmallVec<[GenericArg<'db>; 8]>;

pub struct TypeWalker<'db> {
    stack: TypeWalkerStack<'db>,
    last_subtree: usize,
    pub visited: FxHashSet<GenericArg<'db>>,
}

/// An iterator for walking the type tree.
///
/// It's very easy to produce a deeply
/// nested type tree with a lot of
/// identical subtrees. In order to work efficiently
/// in this situation walker only visits each type once.
/// It maintains a set of visited types and
/// skips any types that are already there.
impl<'db> TypeWalker<'db> {
    pub fn new(root: GenericArg<'db>) -> Self {
        Self { stack: smallvec![root], last_subtree: 1, visited: FxHashSet::default() }
    }

    /// Skips the subtree corresponding to the last type
    /// returned by `next()`.
    ///
    /// Example: Imagine you are walking `Foo<Bar<i32>, usize>`.
    ///
    /// ```ignore (illustrative)
    /// let mut iter: TypeWalker = ...;
    /// iter.next(); // yields Foo
    /// iter.next(); // yields Bar<i32>
    /// iter.skip_current_subtree(); // skips i32
    /// iter.next(); // yields usize
    /// ```
    pub fn skip_current_subtree(&mut self) {
        self.stack.truncate(self.last_subtree);
    }
}

impl<'db> Iterator for TypeWalker<'db> {
    type Item = GenericArg<'db>;

    fn next(&mut self) -> Option<GenericArg<'db>> {
        debug!("next(): stack={:?}", self.stack);
        loop {
            let next = self.stack.pop()?;
            self.last_subtree = self.stack.len();
            if self.visited.insert(next.clone()) {
                push_inner(&mut self.stack, next.clone());
                debug!("next: stack={:?}", self.stack);
                return Some(next);
            }
        }
    }
}

impl<'db> GenericArg<'db> {
    /// Iterator that walks `self` and any types reachable from
    /// `self`, in depth-first order. Note that just walks the types
    /// that appear in `self`, it does not descend into the fields of
    /// structs or variants. For example:
    ///
    /// ```text
    /// isize => { isize }
    /// Foo<Bar<isize>> => { Foo<Bar<isize>>, Bar<isize>, isize }
    /// [isize] => { [isize], isize }
    /// ```
    pub fn walk(self) -> TypeWalker<'db> {
        TypeWalker::new(self)
    }
}

impl<'db> Ty<'db> {
    /// Iterator that walks `self` and any types reachable from
    /// `self`, in depth-first order. Note that just walks the types
    /// that appear in `self`, it does not descend into the fields of
    /// structs or variants. For example:
    ///
    /// ```text
    /// isize => { isize }
    /// Foo<Bar<isize>> => { Foo<Bar<isize>>, Bar<isize>, isize }
    /// [isize] => { [isize], isize }
    /// ```
    pub fn walk(self) -> TypeWalker<'db> {
        TypeWalker::new(self.into())
    }
}

impl<'db> Const<'db> {
    /// Iterator that walks `self` and any types reachable from
    /// `self`, in depth-first order. Note that just walks the types
    /// that appear in `self`, it does not descend into the fields of
    /// structs or variants. For example:
    ///
    /// ```text
    /// isize => { isize }
    /// Foo<Bar<isize>> => { Foo<Bar<isize>>, Bar<isize>, isize }
    /// [isize] => { [isize], isize }
    /// ```
    pub fn walk(self) -> TypeWalker<'db> {
        TypeWalker::new(self.into())
    }
}

/// We push `GenericArg`s on the stack in reverse order so as to
/// maintain a pre-order traversal. As of the time of this
/// writing, the fact that the traversal is pre-order is not
/// known to be significant to any code, but it seems like the
/// natural order one would expect (basically, the order of the
/// types as they are written).
fn push_inner<'db>(stack: &mut TypeWalkerStack<'db>, parent: GenericArg<'db>) {
    match parent.kind() {
        GenericArgKind::Type(parent_ty) => match parent_ty.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Infer(_)
            | TyKind::Param(_)
            | TyKind::Never
            | TyKind::Error(_)
            | TyKind::Placeholder(..)
            | TyKind::Bound(..)
            | TyKind::Foreign(..) => {}

            TyKind::Pat(ty, pat) => {
                stack.push(ty.into());
            }
            TyKind::Array(ty, len) => {
                stack.push(len.into());
                stack.push(ty.into());
            }
            TyKind::Slice(ty) => {
                stack.push(ty.into());
            }
            TyKind::RawPtr(ty, _) => {
                stack.push(ty.into());
            }
            TyKind::Ref(lt, ty, _) => {
                stack.push(ty.into());
                stack.push(lt.into());
            }
            TyKind::Alias(_, data) => {
                stack.extend(data.args.iter().rev());
            }
            TyKind::Dynamic(obj, lt, _) => {
                stack.push(lt.into());
                stack.extend(obj.iter().rev().flat_map(|predicate| {
                    let (args, opt_ty) = match predicate.skip_binder() {
                        ExistentialPredicate::Trait(tr) => (tr.args, None),
                        ExistentialPredicate::Projection(p) => (p.args, Some(p.term)),
                        ExistentialPredicate::AutoTrait(_) =>
                        // Empty iterator
                        {
                            (GenericArgs::new_from_iter(DbInterner::new(), []), None)
                        }
                    };

                    args.iter().rev().chain(opt_ty.map(|term| match term.kind() {
                        TermKind::Ty(ty) => ty.into(),
                        TermKind::Const(ct) => ct.into(),
                    }))
                }));
            }
            TyKind::Adt(_, args)
            | TyKind::Closure(_, args)
            | TyKind::CoroutineClosure(_, args)
            | TyKind::Coroutine(_, args)
            | TyKind::CoroutineWitness(_, args)
            | TyKind::FnDef(_, args) => {
                stack.extend(args.iter().rev());
            }
            TyKind::Tuple(ts) => stack.extend(ts.iter().rev().map(GenericArg::from)),
            TyKind::FnPtr(sig_tys, _hdr) => {
                stack.extend(
                    sig_tys.skip_binder().inputs_and_output.iter().rev().map(|ty| ty.into()),
                );
            }
            TyKind::UnsafeBinder(..) => todo!(),
        },
        GenericArgKind::Lifetime(_) => {}
        GenericArgKind::Const(parent_ct) => match parent_ct.kind() {
            ConstKind::Infer(_)
            | ConstKind::Param(_)
            | ConstKind::Placeholder(_)
            | ConstKind::Bound(..)
            | ConstKind::Error(_) => {}

            ConstKind::Value(vc) => stack.push(vc.ty.into()),

            ConstKind::Expr(expr) => stack.extend(expr.args().iter().rev()),
            ConstKind::Unevaluated(ct) => {
                stack.extend(ct.args.iter().rev());
            }
        },
    }
}
