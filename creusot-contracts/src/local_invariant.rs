use crate::{logic::Set, *};

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
pub struct LocalInvariant<T> {
    value: T,
    initial_value: Snapshot<T>,
    namespace: Snapshot<Namespace>,
}

impl<T: Invariant> LocalInvariant<T> {
    #[ensures(result.init() == value)]
    #[ensures(result.namespace() == *namespace)]
    pub fn new(value: T, namespace: Snapshot<Namespace>) -> Self {
        let _ = namespace;
        Self { initial_value: snapshot!(value), namespace, value }
    }

    /// Get the namespace associated with this invariant.
    #[logic]
    #[open(self)]
    pub fn namespace(self) -> Namespace {
        *self.namespace
    }

    /// Get the initial value with which this invariant was initialized.
    #[logic]
    #[open(self)]
    pub fn init(self) -> T {
        *self.initial_value
    }

    #[trusted]
    #[requires(namespace.contains(self.namespace()))]
    #[ensures((^namespace.inner_logic()) == (*namespace.inner_logic()).remove(self.namespace()))] // UHHH, no ?
    // TODO: tis a bit sad that T cannot use external data as its invariant (aka `init`)
    pub fn open(&self, namespace: Ghost<&mut Set<Namespace>>) -> &mut T {
        let _ = namespace;
        todo!()
    }
}
