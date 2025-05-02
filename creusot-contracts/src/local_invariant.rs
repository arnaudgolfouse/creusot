//! Define local invariants
//!
//! [Local invariants](LocalInvariant) are not the same as [invariants](Invariant): they
//! allow the use of a shared piece of data to be used in the invariant (see
//! [`LocalInvariantSpec`]), but in return they impose a much more restricted access to
//! the underlying data, as well as the use of [`Namespaces`].

use crate::{logic::Set, *};
use ::std::cell::UnsafeCell;

/// Declare a new namespace.
///
/// # Example
///
/// ```rust
/// use creusot_contracts::{*, local_invariant::{declare_namespace, Namespace}, logic::Set};
/// declare_namespace! { A }
///
/// #[requires(ns.contains(A()))]
/// fn foo(ns: Ghost<&mut Set<Namespace>>) { /* ... */ }
/// ```
pub use base_macros::declare_namespace;

/// The type of _namespaces_ associated with invariants.
///
/// Can be declared with the [`declare_namespace`] macro, and then attached to a local
/// invariant when creating it with [`LocalInvariant::new`].
#[cfg_attr(creusot, rustc_diagnostic_item = "namespace_ty")]
pub struct Namespace(());

impl Namespace {
    /// Used by [`declare_namespace`].
    #[logic]
    #[open(self)]
    #[requires(false)]
    #[doc(hidden)]
    pub fn new() -> Self {
        Self(())
    }
}

/// A collection of namespaces.
///
/// This is given at the start of the program, and must be passed along to [LocalInvariant::open].
pub struct Namespaces<'a>(::std::marker::PhantomData<&'a mut Vec<Namespace>>);

impl Namespaces<'_> {
    #[logic]
    #[open(self)]
    #[trusted]
    pub fn namespaces(self) -> Set<Namespace> {
        dead
    }

    #[ensures((*self).namespaces() == result.namespaces())]
    #[ensures((^self).namespaces() == result.namespaces())]
    #[trusted]
    pub fn reborrow(&mut self) -> Namespaces {
        Namespaces(::std::marker::PhantomData)
    }
}

impl View for Namespaces<'_> {
    type ViewTy = Set<Namespace>;
    #[logic]
    #[open]
    fn view(self) -> Set<Namespace> {
        self.namespaces()
    }
}

pub struct LocalInvariant<T, D> {
    value: UnsafeCell<T>,
    #[cfg_attr(not(creusot), allow(unused))]
    public: Snapshot<D>,
    #[cfg_attr(not(creusot), allow(unused))]
    namespace: Snapshot<Namespace>,
}

pub trait LocalInvariantSpec<D> {
    #[predicate]
    fn invariant_with_data(self, data: D) -> bool;
}

impl<D, T: LocalInvariantSpec<D>> LocalInvariant<T, D> {
    /// Construct a `LocalInvariant`
    ///
    /// # Parameters
    /// - `value`: the actual data contained in the invariant. Use [`Self::open`] to
    /// access it. Also called the 'private' part of the invariant.
    /// - `public`: the 'public' part of the invariant.
    /// - `namespace`: the namespace of the invariant.
    ///   This is required to avoid [open](Self::open)ing the same invariant twice.
    #[requires(value.invariant_with_data(*public))]
    #[ensures(result.public() == *public)]
    #[ensures(result.namespace() == *namespace)]
    pub fn new(value: T, public: Snapshot<D>, namespace: Snapshot<Namespace>) -> Self {
        Self { value: UnsafeCell::new(value), public, namespace }
    }

    /// Get the namespace associated with this invariant.
    #[logic]
    #[open(self)]
    pub fn namespace(self) -> Namespace {
        *self.namespace
    }

    /// Get the 'public' part of this invariant.
    #[logic]
    #[open(self)]
    pub fn public(self) -> D {
        *self.public
    }

    /// Open the invariant to get the data stored inside.
    ///
    /// This will call the closure `f` with the inner data. You must restore the
    /// contained [`LocalInvariantSpec`] before returning from the closure.
    ///
    /// # Safety
    ///
    /// When the program is verified using Creusot, this function is safe to call.
    /// Else, you **must** ensure that this invariant is not opened again in the closure.
    #[trusted]
    #[requires(namespaces@.contains(self.namespace()))]
    #[requires(forall<t: &mut T> (*t).invariant_with_data(self.public()) ==>
        f.precondition((t,)) &&
        // f must restore the invariant
        (forall<res: A> f.postcondition_once((t,), res) ==> (^t).invariant_with_data(self.public())))]
    #[ensures((**result.1).invariant_with_data(self.public()) && f.postcondition_once((*result.1,), result.0))]
    pub unsafe fn open<'a, A>(
        &'a self,
        namespaces: Namespaces<'a>,
        f: impl FnOnce(&'a mut T) -> A,
    ) -> (A, Snapshot<&'a mut T>) {
        let _ = namespaces;
        let borrow = unsafe { &mut *self.value.get() };
        let res1 = snapshot!(borrow);
        (f(borrow), res1)
    }
}
