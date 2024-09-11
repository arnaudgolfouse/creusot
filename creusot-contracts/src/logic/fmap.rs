use crate::{logic::Mapping, util::*, *};

type PMap<K, V> = Mapping<K, Option<SizedW<V>>>;

/// A Map type usable in specs and `ghost!` blocks.
///
/// # Ghost
///
/// Since [`std::collections::HashMap`] and [`std::collections::BTreeMap`] have finite
/// capacity, this could cause some issues in ghost code:
/// ```rust,creusot,compile_fail
/// ghost! {
///     let mut map = HashMap::new();
///     for _ in 0..=usize::MAX as u128 + 1 {
///         map.insert(0, 0); // cannot fail, since we are in a ghost block
///     }
///     proof_assert!(map.len_logic() <= usize::MAX); // by definition
///     proof_assert!(map.len_logic() > usize::MAX); // uh-oh
/// }
/// ```
///
/// This type is designed for this use-case, with no restriction on the capacity.
#[trusted] //opaque
pub struct FMap<K, V: ?Sized>(PMap<K, V>);

/// Logical definitions
impl<K, V: ?Sized> FMap<K, V> {
    #[trusted]
    #[logic]
    #[open(self)]
    #[ensures(result >= 0)]
    pub fn len_logic(self) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    pub fn mk(_m: PMap<K, V>) -> Self {
        absurd
    }

    #[trusted]
    #[open(self)]
    #[logic]
    #[ensures(Self::mk(result) == self)] // injectivity
    pub fn view(self) -> PMap<K, V> {
        absurd
    }

    #[trusted]
    #[open(self)]
    #[logic]
    #[ensures(result.view() == self.view().set(k, Some(v.make_sized())))]
    #[ensures(self.contains_logic(k) ==> result.len_logic() == self.len_logic())]
    #[ensures(!self.contains_logic(k) ==> result.len_logic() == self.len_logic() + 1)]
    pub fn insert_logic(self, k: K, v: V) -> Self {
        absurd
    }

    #[trusted]
    #[open(self)]
    #[logic]
    #[ensures(result.view() == self.view().set(k, None))]
    #[ensures(result.len_logic() == if self.contains_logic(k) {self.len_logic() - 1} else {self.len_logic()})]
    pub fn remove_logic(self, k: K) -> Self {
        absurd
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn get_logic(self, k: K) -> Option<SizedW<V>> {
        self.view().get(k)
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn lookup_unsized(self, k: K) -> SizedW<V> {
        unwrap(self.get_logic(k))
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn lookup(self, k: K) -> V
    where
        V: Sized,
    {
        *self.lookup_unsized(k)
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn contains_logic(self, k: K) -> bool {
        self.get_logic(k) != None
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[ensures(result.len_logic() == 0)]
    #[ensures(result.view() == Mapping::cst(None))]
    pub fn empty() -> Self {
        absurd
    }

    #[logic]
    #[open]
    pub fn is_empty(self) -> bool {
        self.ext_eq(FMap::empty())
    }

    #[logic]
    #[open]
    pub fn disjoint(self, other: Self) -> bool {
        pearlite! {forall<k: K> !self.contains_logic(k) || !other.contains_logic(k)}
    }

    #[logic]
    #[open]
    pub fn subset(self, other: Self) -> bool {
        pearlite! {forall<k: K> self.contains_logic(k) ==> other.get_logic(k) == self.get_logic(k)}
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[requires(self.disjoint(other))]
    #[ensures(forall<k: K> result.get_logic(k) == if self.contains_logic(k) {
        self.get_logic(k)
    } else if other.contains_logic(k) {
        other.get_logic(k)
    } else {
        None
    })]
    #[ensures(result.len_logic() == self.len_logic() + other.len_logic())]
    pub fn union(self, other: Self) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[ensures(forall<k: K> result.get_logic(k) == if other.contains_logic(k) {None} else {self.get_logic(k)})]
    pub fn subtract_keys(self, other: Self) -> Self {
        absurd
    }

    #[logic]
    #[open]
    #[requires(other.subset(self))]
    #[ensures(result.disjoint(other))]
    #[ensures(other.union(result).ext_eq(self))]
    #[ensures(forall<k: K> result.get_logic(k) == if other.contains_logic(k) {None} else {self.get_logic(k)})]
    pub fn subtract(self, other: Self) -> Self {
        self.subtract_keys(other)
    }

    #[logic]
    #[open]
    #[ensures(result ==> self == other)]
    #[ensures((forall<k: K> self.get_logic(k) == other.get_logic(k)) ==> result)]
    pub fn ext_eq(self, other: Self) -> bool {
        self.view() == other.view()
    }
}

/// Ghost definitions
impl<K, V: ?Sized> FMap<K, V> {
    #[trusted]
    #[pure]
    #[ensures(result.is_empty())]
    /// Create a new, empty map on the ghost heap.
    pub fn new_ghost() -> GhostBox<Self> {
        GhostBox::from_fn(|| loop {})
    }

    /// Returns the number of elements in the map.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new_ghost();
    /// let lengths = ghost! {
    ///     let len1 = map.len();
    ///     map.insert(1, 21);
    ///     map.insert(1, 42);
    ///     map.insert(2, 50);
    ///     let len2 = map.len();
    ///     (len1, len2)
    /// };
    /// proof_assert!(length.inner().0 == 0);
    /// proof_assert!(length.inner().1 == 2);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(result == self.len_logic())]
    pub fn len(&self) -> Int {
        loop {}
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new_ghost();
    /// let contains = ghost! {
    ///     map.insert(1, 42);
    ///     (map.contains(&1), map.contains(&2))
    /// };
    /// proof_assert!(contains.inner().0);
    /// proof_assert!(!contains.inner().1);
    /// ```
    #[pure]
    #[ensures(self.contains_logic(*key))]
    pub fn contains(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new_ghost();
    /// ghost! {
    ///     map.insert(1, 2);
    ///     proof_assert!(map.get_logic(&1) == Some(&2));
    ///     proof_assert!(map.get_logic(&2) == None);
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self.contains_logic(*key) {
            match result {
                None => false,
                Some(r) => *self.lookup_unsized(*key) == *r,
            }
        } else {
            result == None
        })]
    pub fn get(&self, key: &K) -> Option<&V> {
        let _ = key;
        loop {}
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new_ghost();
    /// ghost! {
    ///     map.insert(1, 21);
    ///     if let Some(x) = map.get_mut(&1) {
    ///         *x = 42;
    ///     }
    /// };
    /// proof_assert!(map.lookup(1i32) == 42i32);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self.contains_logic(*key) {
            match result {
                None => false,
                Some(r) => *(*self).lookup_unsized(*key) == *r &&
                           *(^self).lookup_unsized(*key) == ^r,
            }
        } else {
            result == None
        })]
    #[ensures(forall<k: K> k != *key ==> (*self).get_logic(k) == (^self).get_logic(k))]
    #[ensures((*self).len_logic() == (^self).len_logic())]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let _ = key;
        loop {}
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new_ghost();
    /// ghost! {
    ///     proof_assert!(map.insert_logic(37, 41) == None);
    ///     proof_assert!(map.is_empty() == false);
    ///
    ///     map.insert(37, 42);
    ///     proof_assert!(map.insert_logic(37, 43) == Some(42));
    ///     proof_assert!(map.get_logic(&37) == Some(&43));
    /// };
    /// ```
    #[trusted]
    #[pure]
    #[ensures(^self == self.insert_logic(key, value))]
    #[ensures(if self.contains_logic(key) {
            result == Some(self.lookup(key))
        } else {
            result == None
        })]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        V: Sized,
    {
        let _ = key;
        let _ = value;
        loop {}
    }

    /// Same as [`Self::insert`], but for unsized values.
    #[trusted]
    #[pure]
    #[ensures(^self == self.insert_logic(key, *value))]
    #[ensures(if self.contains_logic(key) {
            result == Some(self.lookup_unsized(key))
        } else {
            result == None
        })]
    pub fn insert_unsized(&mut self, key: K, value: Box<V>) -> Option<Box<V>> {
        let _ = key;
        let _ = value;
        loop {}
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{logic::FMap, *};
    ///
    /// let mut map = FMap::new_ghost();
    /// let res = ghost! {
    ///     map.insert(1, 42);
    ///     let res1 = map.remove(&1);
    ///     let res2 = map.remove(&1);
    ///     (res1, res2)
    /// };
    /// proof_assert!(res.0 == Some(42i32));
    /// proof_assert!(res.1 == None);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(^self == self.remove_logic(*key))]
    #[ensures(match self.get_logic(*key) {
            None => result == None,
            Some(v) => result == Some(*v),
        })]
    pub fn remove(&mut self, key: &K) -> Option<V>
    where
        V: Sized,
    {
        let _ = key;
        loop {}
    }

    /// Same as [`Self::remove`], but for unsized values.
    #[trusted]
    #[pure]
    #[ensures(^self == self.remove_logic(*key))]
    #[ensures(self.get_logic(*key) == None)]
    pub fn remove_unsized(&mut self, key: &K) -> Option<Box<V>> {
        let _ = key;
        loop {}
    }
}
