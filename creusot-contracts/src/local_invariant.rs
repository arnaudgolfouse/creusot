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
/// FIXME: more docs
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

#[allow(dead_code)] // FIXME
pub struct LocalInvariant<T, D> {
    value: UnsafeCell<T>,
    data: Snapshot<D>,
    namespace: Snapshot<Namespace>,
}

pub trait LocalInvariantSpec<D> {
    #[predicate]
    fn invariant_with_data(self, data: D) -> bool;
}

/// Type returned by [`LocalInvariant::open`].
///
/// This is a proxy for `&'a mut T`, with an additional invariant [depending on `D`](LocalInvariantSpec).
pub struct OpenLocalInv<'a, T, D> {
    #[cfg_attr(not(creusot), allow(unused))]
    data: Snapshot<D>,
    value: &'a mut T,
}

#[cfg_attr(not(creusot), allow(clippy::needless_lifetimes))]
impl<'a, T, D> OpenLocalInv<'a, T, D> {
    /// Get the additionnal data associated with the invariant.
    ///
    /// This is the data that was passed in [`LocalInvariant::new`], and the one used in
    /// [`LocalInvariantSpec`].
    #[logic]
    #[open(self)]
    pub fn data(self) -> D {
        *self.data
    }

    /// Get the contained borrow.
    #[logic]
    #[open(self)]
    pub fn value(self) -> &'a mut T {
        self.value
    }

    /// Use the contained data in a closure.
    ///
    /// The closure is required to restore the [`LocalInvariantSpec`] by the end of its execution.
    #[requires(forall<b: &mut T> *b == *self.value() ==> f.precondition((b,)))]
    #[requires(forall<b: &mut T>
        *b == *self.value() ==>
        (exists<f_fin: _> f.postcondition_mut((b,), f_fin, ())) ==>
        (^b).invariant_with_data(self.data()))]
    #[ensures((*self.value()).invariant_with_data(self.data()))]
    #[ensures((*self).data() == (^self).data())]
    #[ensures(exists<b: &mut T, f_fin: _>
        *b == *self.value() &&
        f.postcondition_mut((b,), f_fin, ()) &&
        *(^self).value() == ^b)]
    #[ensures(^(*self).value() == ^(^self).value())]
    pub fn open(&mut self, mut f: impl FnMut(&mut T))
    where
        T: LocalInvariantSpec<D>,
    {
        f(&mut *self.value)
    }
}

impl<T, D> Resolve for OpenLocalInv<'_, T, D> {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        resolve(&self.value())
    }

    #[logic(prophetic)]
    #[requires(inv(self))]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    #[open]
    fn resolve_coherence(&self) {}
}

impl<D, T: LocalInvariantSpec<D>> Invariant for OpenLocalInv<'_, T, D> {
    #[predicate(prophetic)]
    #[open]
    fn invariant(self) -> bool {
        pearlite! {
            (*self.value()).invariant_with_data(self.data())
                && (^self.value()).invariant_with_data(self.data())
        }
    }
}

impl<D, T: LocalInvariantSpec<D>> LocalInvariant<T, D> {
    #[requires(value.invariant_with_data(*data))]
    #[ensures(result.data() == *data)]
    #[ensures(result.namespace() == *namespace)]
    pub fn new(value: T, data: Snapshot<D>, namespace: Snapshot<Namespace>) -> Self {
        Self { value: UnsafeCell::new(value), data, namespace }
    }

    /// Get the namespace associated with this invariant.
    #[logic]
    #[open(self)]
    pub fn namespace(self) -> Namespace {
        *self.namespace
    }

    /// Get the data used to create this invariant.
    #[logic]
    #[open(self)]
    pub fn data(self) -> D {
        *self.data
    }

    /// # Safety
    ///
    /// Do not use without verifiying your program with Creusot ;)
    #[trusted]
    #[pure]
    #[requires(namespace.contains(self.namespace()))]
    #[ensures((^namespace.inner_logic()) == (*namespace.inner_logic()).remove(self.namespace()))]
    pub unsafe fn open(&self, namespaces: Ghost<&mut Set<Namespace>>) -> OpenLocalInv<T, D> {
        let _ = namespaces;
        OpenLocalInv { data: self.data, value: unsafe { &mut *self.value.get() } }
    }
}
