use crate::{
    logic::{ops::IndexLogic, Mapping},
    *,
};

/// A [`Vec`] type usable in `ghost!` blocks.
///
/// # Logic
///
/// This type is (in particular) the logical representation of a [`Vec`]. This can be
/// accessed via its [shallow model](crate::ShallowModel) (The `@` operator).
///
/// ```rust,creusot
/// use creusot_contracts::*;
///
/// #[logic]
/// #[open]
/// fn get_model<T>(v: Vec<T>) -> Seq<T> {
///     pearlite!(v@)
/// }
/// ```
///
/// # Ghost
///
/// Since [`Vec`] have finite capacity, this could cause some issues in ghost code:
/// ```rust,creusot,compile_fail
/// ghost! {
///     let mut v = Vec::new();
///     for _ in 0..=usize::MAX as u128 + 1 {
///         v.push(0); // cannot fail, since we are in a ghost block
///     }
///     proof_assert!(v.len() <= usize::MAX); // by definition
///     proof_assert!(v.len() > usize::MAX); // uh-oh
/// }
/// ```
///
/// This type is designed for this use-case, with no restriction on the capacity.
#[cfg_attr(creusot, creusot::builtins = "seq.Seq.seq")]
pub struct Seq<T: ?Sized>(std::marker::PhantomData<T>);

/// Logical definitions
impl<T> Seq<T> {
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "seq.Seq.empty"]
    pub const EMPTY: Self = { Seq(std::marker::PhantomData) };

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.create"]
    pub fn new(_: Int, _: Mapping<Int, T>) -> Self {
        absurd
    }

    #[logic]
    #[open]
    pub fn get_logic(self, ix: Int) -> Option<T> {
        if 0 <= ix && ix < self.len_logic() {
            Some(self.index_logic(ix))
        } else {
            None
        }
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "prelude.seq_ext.SeqExt.subsequence"]
    pub fn subsequence(self, _: Int, _: Int) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.singleton"]
    pub fn singleton(_: T) -> Self {
        absurd
    }

    #[logic]
    #[open]
    pub fn tail(self) -> Self {
        self.subsequence(1, self.len_logic())
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[rustc_diagnostic_item = "seq_len"]
    #[creusot::builtins = "seq.Seq.length"]
    pub fn len_logic(self) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.set"]
    pub fn set(self, _: Int, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.(==)"]
    pub fn ext_eq(self, _: Self) -> bool {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push_logic(self, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.(++)"]
    pub fn concat(self, _: Self) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Reverse.reverse"]
    pub fn reverse_logic(self) -> Self {
        absurd
    }

    #[predicate]
    #[open]
    pub fn permutation_of(self, o: Self) -> bool {
        self.permut(o, 0, self.len_logic())
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Permut.permut"]
    pub fn permut(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Permut.exchange"]
    pub fn exchange(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[open]
    #[predicate]
    pub fn contains_logic(self, e: T) -> bool {
        pearlite! { exists<i : Int> 0 <= i &&  i <self.len_logic() && self[i] == e }
    }

    #[open]
    #[predicate]
    pub fn sorted_range(self, l: Int, u: Int) -> bool
    where
        T: OrdLogic,
    {
        pearlite! {
            forall<i : Int, j : Int> l <= i && i <= j && j < u ==> self[i] <= self[j]
        }
    }

    #[open]
    #[predicate]
    pub fn sorted(self) -> bool
    where
        T: OrdLogic,
    {
        self.sorted_range(0, self.len_logic())
    }
}

/// Ghost definitions
impl<T> Seq<T> {
    /// Constructs a new, empty `Seq<T>`.
    ///
    /// This is allocated on the ghost heap, and as such is wrapped in [`GhostBox`].
    ///
    /// # Example
    ///
    /// ```rust,creusot
    /// use creusot_contracts::{proof_assert, Seq};
    /// let ghost_seq = Seq::<i32>::new_ghost();
    /// proof_assert!(seq == Seq::new());
    /// ```
    #[trusted]
    #[pure]
    #[ensures(*result == Self::EMPTY)]
    pub fn new_ghost() -> GhostBox<Self> {
        GhostBox::from_fn(|| loop {})
    }

    /// Returns the number of elements in the vector, also referred to as its 'length'.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut vec = Seq::new_ghost();
    /// let length = ghost! {
    ///     vec.push(1);
    ///     vec.push(2);
    ///     vec.push(3);
    ///     vec.len()
    /// };
    /// proof_assert!(length.inner() == 3);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(result == self.len_logic())]
    pub fn len(&self) -> Int {
        loop {}
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new_ghost();
    /// ghost! {
    ///     s.push(1);
    ///     s.push(2);
    ///     s.push(3);
    /// };
    /// proof_assert!(s[0] == 1i32 && s[1] == 2i32 && s[2] == 3i32);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(^self == self.push_logic(x))]
    pub fn push(&mut self, x: T) {
        let _ = x;
        loop {}
    }

    /// Returns a reference to an element at `index` or `None` if `index` is out of bounds.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, Int, proof_assert, Seq};
    ///
    /// let mut s = Seq::new_ghost();
    /// let gets = ghost! {
    ///     s.push(10);
    ///     s.push(40);
    ///     s.push(30);
    ///     let get1 = s.get(*Int::new(1));
    ///     let get2 = s.get(*Int::new(3));
    ///     (get1, get2)
    /// };
    /// proof_assert!(gets.inner().0 == Some(&40i32));
    /// proof_assert!(gets.inner().1 == None);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(match self.get_logic(index) {
        None => result == None,
        Some(v) => result == Some(&v),
    })]
    pub fn get(&self, index: Int) -> Option<&T> {
        let _ = index;
        loop {}
    }

    /// Returns a mutable reference to an element at `index` or `None` if `index` is out of bounds.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, Int, proof_assert, Seq};
    ///
    /// let mut s = Seq::new_ghost();
    ///
    /// ghost! {
    ///     s.push(0);
    ///     s.push(1);
    ///     s.push(2);
    ///     if let Some(elem) = s.get_mut(*Int::new(1)) {
    ///         *elem = 42;
    ///     }
    /// };
    /// proof_assert!(s[0] == 0i32 && s[1] == 42i32 && s[2] == 2i32);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self.get_logic(index) == None {
        result == None && *self == ^self
    } else {
        match result {
            None => false,
            Some(r) => *r == (*self)[index] && ^r == (^self)[index]
        }
    })]
    #[ensures(forall<i: Int> i != index ==> (*self).get_logic(index) == (^self).get_logic(index))]
    #[ensures((*self).len_logic() == (^self).len_logic())]
    pub fn get_mut(&mut self, index: Int) -> Option<&mut T> {
        let _ = index;
        loop {}
    }

    /// Removes the last element from a vector and returns it, or `None` if it is empty.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new_ghost();
    /// let popped = ghost! {
    ///     s.push(1);
    ///     s.push(2);
    ///     s.push(3);
    ///     s.pop()
    /// };
    /// proof_assert!(popped == Some(3i32));
    /// proof_assert!(s[0] == 1i32 && s[1] == 2i32);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self.len_logic() == 0 {
        *self == ^self && result == None
    } else {
        match result {
            None => false,
            Some(r) => *self == (^self).push_logic(r)
        }
    })]
    pub fn pop(&mut self) -> Option<T> {
        loop {}
    }
}

impl<T> Seq<&T> {
    #[logic]
    #[open]
    #[trusted]
    #[creusot::builtins = "prelude.prelude.Seq.to_owned"]
    pub fn to_owned_seq(self) -> Seq<T> {
        pearlite! {absurd}
    }
}

impl<T> IndexLogic<Int> for Seq<T> {
    type Item = T;

    #[logic]
    #[trusted]
    #[open(self)]
    #[rustc_diagnostic_item = "seq_index"]
    #[creusot::builtins = "seq.Seq.get"]
    fn index_logic(self, _: Int) -> Self::Item {
        absurd
    }
}
