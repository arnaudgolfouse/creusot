// TACTIC +compute_in_goal

extern crate creusot_contracts;

pub mod implementation {
    use ::std::rc::Rc;
    use creusot_contracts::{
        Clone,
        local_invariant::{LocalInvariant, LocalInvariantSpec, Namespaces, declare_namespace},
        logic::{FMap, Mapping},
        pcell::{Id, PCell, PCellOwn},
        resource::gmap::GMap,
        *,
    };

    declare_namespace! { PARRAY }

    /// Type of values stored in the array
    // FIXME: replace with polymorphism
    type Value = i32;

    type PersistentArrayInvariant = LocalInvariant<TokensMapInner, Id>;

    /// A type of persistent arrays
    ///
    /// Persistent arrays have the following properties:
    /// - they can be freely (and cheaply) cloned
    /// - they can cheaply create new modified versions, without affecting the other copies
    ///
    /// # Safety
    ///
    /// All methods marked `unsafe` are actually safe to use, _as long as you check the
    /// program with Creusot_.
    ///
    /// If you don't, you must ensure that a [`TokensMap`] object is never used with a
    /// `PersistentArray` that is not derived from it.
    #[derive(Clone)]
    pub struct PersistentArray {
        /// Contains a pointer to the actual value
        program_value: Rc<PCell<Inner>>,
        /// Fraction of the GMap resource.
        ///
        /// This contains a fraction of the map, with only `program_value.id()` as key.
        /// The corresponding value is the logical value of the map.
        contained_in_token: Ghost<&'static GMap<Id, Seq<Value>>>,
        /// The [`Id`] in the public part is the id of the whole `GMap`, **not** the individual keys !
        ///
        /// FIXME: not ghost, this will be an issue.
        map_invariant: &'static PersistentArrayInvariant,
    }

    impl Invariant for PersistentArray {
        #[predicate]
        #[open(self)]
        fn invariant(self) -> bool {
            pearlite! {
                // We indeed have the corresponding fractional part of the invariant
                self.contained_in_token.is_frac()
                && self.contained_in_token.frac().contains(self.program_value@.id())
                && self.contained_in_token.id() == self.map_invariant.public()
                && self.map_invariant.namespace() == PARRAY()
            }
        }
    }

    enum Inner {
        Direct(Vec<Value>),
        Link { index: usize, value: Value, next: Rc<PCell<Inner>> },
    }

    impl View for PersistentArray {
        type ViewTy = Seq<Value>;
        #[logic]
        #[open(self)]
        fn view(self) -> Seq<Value> {
            pearlite! {
                self.contained_in_token.frac().lookup(self.program_value@.id())
            }
        }
    }

    type LogicId = Snapshot<Id>;
    type OwnMap = FMap<LogicId, PCellOwn<Inner>>;

    /// Actual structure of the map, with a local invariant.
    struct TokensMapInner {
        own_map: Ghost<OwnMap>,
        values: Ghost<GMap<Id, Seq<Value>>>,
        rank: Snapshot<Mapping<Id, Int>>,
        length: Snapshot<Int>,
    }

    impl LocalInvariantSpec<Id> for TokensMapInner {
        #[predicate]
        #[open(self)]
        fn invariant_with_data(self, id: Id) -> bool {
            let values = self.values.auth();
            pearlite! {
                self.values.is_auth() &&
                self.values.id() == id &&
                (forall<id: LogicId> self.own_map.contains(id) == values.contains(*id)) &&
                (forall<id: LogicId> self.own_map.contains(id) ==> self.own_map[id].id() == *id) &&
                (forall<id: LogicId> self.own_map.contains(id) ==> values.lookup(*id).len() == *self.length) &&
                // If `Link { next, .. }` is in the map, then `next` is also in the map.
                (forall<id: LogicId> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(_) => true,
                    Inner::Link { next, .. } => self.own_map.contains(Snapshot::new(next@.id())),
                }) &&
                // The array in `self.values` agrees with the one in `self.own_map`
                (forall<id: LogicId> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(v) => values.lookup(*id) == v@,
                    Inner::Link { index, value, next } => {
                        let next_id = next@.id();
                        index@ < *self.length &&
                        values.lookup(*id)[index@] == value &&
                        (forall<j: Int> 0 <= j && j < *self.length && j != index@ ==> values.lookup(*id)[j] == values.lookup(next_id)[j])
                    },
                }) &&
                // The rank decreases when following the links
                (forall<id: LogicId> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(_) => true,
                    Inner::Link { next, .. } => {
                        let next_id = next@.id();
                        self.rank[*id] > self.rank[next_id]
                    },
                })
            }
        }
    }

    impl PersistentArray {
        /// Create a new array from the given vector of values
        #[ensures(result@ == v@)]
        pub fn new(v: Vec<Value>) -> Self {
            let logical_value = snapshot!(v@);
            let (program_value, ownership) = PCell::new(Inner::Direct(v));
            let id = snapshot!(ownership.id());
            let length = snapshot!(logical_value.len());
            let mut resource = GMap::new();
            let frac_part = ghost!(resource.insert(id, logical_value));
            let gset_id = snapshot!(frac_part.id());

            let own_map = ghost! {
                let mut own_map = FMap::new().into_inner();
                own_map.insert_ghost(id, ownership.into_inner());
                own_map
            };
            let map_invariant = &*Box::leak(Box::new(LocalInvariant::new(
                TokensMapInner { own_map, values: resource, rank: snapshot!(|_| 0), length },
                snapshot!(*gset_id),
                snapshot!(PARRAY()),
            )));

            let this = Self {
                program_value: Rc::new(program_value),
                contained_in_token: ghost!(Box::leak(Box::new(frac_part))),
                map_invariant,
            };

            this
        }

        /// Return a new array, where the value at index `index` has been set to `value`
        #[requires(index@ < self@.len())]
        #[requires(namespaces.contains(PARRAY()))]
        #[ensures(result@ == self@.set(index@, value))]
        pub fn set(&self, index: usize, value: Value, namespaces: Ghost<Namespaces>) -> Self {
            let (program_value, ownership) =
                PCell::new(Inner::Link { index, value, next: self.program_value.clone() });
            let new_frac = {
                let program_value = &program_value;
                unsafe {
                    let public = snapshot!(self.map_invariant.public());
                    self.map_invariant
                        .open(namespaces, |tokens| {
                            // Help closure inference
                            proof_assert!(tokens.invariant_with_data(*public));
                            let cell_id = snapshot!(program_value.id());
                            let self_id = snapshot!(self.program_value@.id());
                            // prove that self is contained in the map by validity
                            ghost! {
                                let _ = tokens.values.contains(*self.contained_in_token);
                            };
                            let new_logical_value = snapshot!(self@.set(index@, value));
                            // prove that we are inserting a _new_ value
                            ghost! {
                                let ownership = ownership.into_inner();
                                match tokens.own_map.get_mut_ghost(&cell_id) {
                                    None => {},
                                    Some(other) => PCellOwn::disjoint_lemma(other, &ownership),
                                }
                                tokens.own_map.insert_ghost(cell_id, ownership);
                                tokens.rank = snapshot! {
                                    let new_distance = tokens.rank[*self_id] + 1;
                                    tokens.rank.set(*cell_id, new_distance)
                                };
                                let frac = tokens.values.insert(cell_id, new_logical_value);
                                &*Box::leak(Box::new(frac))
                            }
                        })
                        .0
                }
            };
            Self {
                program_value: Rc::new(program_value),
                contained_in_token: new_frac,
                map_invariant: self.map_invariant,
            }
        }

        /// Get the value of the array at index `i`.
        ///
        /// If `i` is out of bounds, return `None`.
        ///
        /// # Performances
        ///
        /// If the current array has been obtained after many calls to set, this method
        /// will have to do a lot of pointer chasing to find the value.
        ///
        /// If you use this method often on the same array, consider using [`Self::get`]
        /// instead.
        ///
        /// # Safety
        ///
        /// See the [safety section](PersistentArray#safety) on the type documentation.
        #[requires(namespaces.contains(PARRAY()))]
        #[ensures(if i@ < self@.len() {
            result == Some(&self@[i@])
        } else {
            result == None
        })]
        pub unsafe fn get_immut<'a>(
            &'a self,
            i: usize,
            namespaces: Ghost<Namespaces<'a>>,
        ) -> Option<&'a Value> {
            let public = snapshot!(self.map_invariant.public());
            self.map_invariant
                .open(namespaces, |tokens| {
                    // Help closure inference
                    proof_assert!(tokens.invariant_with_data(*public));
                    // prove that self is contained in the map by validity
                    ghost! {
                        let _ = tokens.values.contains(*self.contained_in_token);
                    };
                    unsafe { Self::get_inner_immut(&self.program_value, i, tokens) }
                })
                .0
        }

        #[requires(exists<p: _> tokens.invariant_with_data(p))]
        #[requires(tokens.own_map.contains(Snapshot::new(inner.view().id())))]
        #[ensures(if i.view() < *tokens.length {
            result == Some(&tokens.values.auth()[inner.view().id()][i.view()])
        } else {
            result == None
        })]
        unsafe fn get_inner_immut<'a>(
            inner: &'a Rc<PCell<Inner>>,
            i: usize,
            tokens: &'a TokensMapInner,
        ) -> Option<&'a Value> {
            let id = snapshot!(inner.view().id());
            let perm = ghost!(tokens.own_map.get_ghost(&id).unwrap());
            let inner = unsafe { inner.as_ref().borrow(perm) };
            match inner {
                Inner::Direct(v) => match v.get(i) {
                    None => None,
                    Some(x) => Some(x),
                },
                Inner::Link { index, value, next } => {
                    if i == *index {
                        Some(value)
                    } else {
                        Self::get_inner_immut(next, i, tokens)
                    }
                }
            }
        }

        /// Get the value of the array at index `i`.
        ///
        /// If `i` is out of bounds, return `None`.
        ///
        /// # Safety
        ///
        /// See the [safety section](PersistentArray#safety) on the type documentation.
        #[requires(namespaces.contains(PARRAY()))]
        #[ensures(if index.view() < self.view().len() {
            result == Some(&self.view()[index.view()])
        } else {
            result == None
        })]
        pub unsafe fn get<'a>(
            &'a self,
            index: usize,
            namespaces: Ghost<Namespaces<'a>>,
        ) -> Option<&'a Value> {
            let public = snapshot!(self.map_invariant.public());
            self.map_invariant
                .open(namespaces, |tokens| {
                    // prove that self is contained in the map by validity
                    ghost! {
                        let _ = tokens.values.contains(*self.contained_in_token);
                    };
                    unsafe { Self::reroot(&self.program_value, public, tokens) };
                    let id = snapshot!(self.program_value.view().id());
                    let perm = ghost!(tokens.own_map.get_ghost(&id).unwrap());
                    let borrow = unsafe { self.program_value.as_ref().borrow(perm) };
                    match borrow {
                        Inner::Direct(arr) => arr.get(index),
                        _ => unreachable!(),
                    }
                })
                .0
        }

        /// Reroot the array: at the end of this function, `inner` will point directly
        /// to the underlying array.
        ///
        /// # Safety
        ///
        /// See the [safety section](PersistentArray#safety) on the type documentation.
        #[requires(tokens.invariant_with_data(*invariant_id))]
        #[requires(tokens.own_map.contains(Snapshot::new(inner.view().id())))]
        #[ensures((^tokens).invariant_with_data(*invariant_id))]
        #[ensures(forall<id: _> (*tokens).own_map.contains(id) == (^tokens).own_map.contains(id))]
        #[ensures((*tokens).values == (^tokens).values)]
        #[ensures((*tokens).length == (^tokens).length)]
        #[ensures(forall<id: Snapshot<_>> (*tokens).rank[*id] > (*tokens).rank[inner.view().id()]
            ==> (*tokens).rank[*id] == (^tokens).rank[*id]
            && (*tokens).own_map.get(id) == (^tokens).own_map.get(id)
        )]
        #[ensures(match *(^tokens).own_map[Snapshot::new(inner.view().id())].val() {
            Inner::Direct(_) => true,
            Inner::Link { .. } => false,
        })]
        #[ensures(*result == (^tokens).rank[inner.view().id()])]
        unsafe fn reroot<'a>(
            inner: &'a Rc<PCell<Inner>>,
            invariant_id: Snapshot<Id>,
            tokens: &'a mut TokensMapInner,
        ) -> Snapshot<Int> {
            let inner_clone = inner.clone();
            let id = snapshot!(inner.view().id());
            let rank = snapshot!(tokens.rank.get(*id));
            let perm = ghost!(tokens.own_map.get_ghost(&id).unwrap());
            let borrow = unsafe { inner.as_ref().borrow(perm) };
            match borrow {
                Inner::Direct(_) => {
                    snapshot!(tokens.rank[*id])
                }
                Inner::Link { next, .. } => {
                    let next = next.clone();
                    let next_id = snapshot!(next.view().id());
                    let next_d = Self::reroot(&next, invariant_id, tokens);

                    let (perm_inner, perm_next) = ghost! {
                        let (p_inner, rest) = tokens.own_map.split_mut_ghost(&id);
                        (p_inner.unwrap(), rest.get_mut_ghost(&next_id).unwrap())
                    }
                    .split();
                    let (bor_inner, bor_next) = unsafe {
                        (inner.as_ref().borrow_mut(perm_inner), next.as_ref().borrow_mut(perm_next))
                    };

                    // This breaks the invariant: now `next` points to itself
                    std::mem::swap(bor_inner, bor_next);

                    // Restore the invariant
                    match (bor_inner, bor_next) {
                        (Inner::Direct(arr), Inner::Link { index, value: value_next, next }) => {
                            *next = inner_clone;
                            std::mem::swap(&mut arr[*index], value_next);
                            let new_d = snapshot!(Int::min(*rank, *next_d - 1));
                            tokens.rank = snapshot!(tokens.rank.set(*id, *new_d));
                            new_d
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
    }
}

macro_rules! seq {
    () => {};
    ( $($e:expr),+ $(,)?) => {
        snapshot!(
            Seq::EMPTY
            $(
                .push_back($e)
            )*
        )
    };
}

use creusot_contracts::{local_invariant::Namespaces, vec, *};
use implementation::PersistentArray;

#[requires(namespaces.contains(implementation::PARRAY()))]
pub fn testing(mut namespaces: Ghost<Namespaces>) {
    let a = PersistentArray::new(vec![1, 2, 3, 4]);

    let a2 = a.set(1, 42, ghost!(namespaces.reborrow()));
    let a3 = a.set(0, 50, ghost!(namespaces.reborrow()));

    let a4 = a.clone();

    let a_model = seq![1i32, 2i32, 3i32, 4i32];
    let a2_model = seq![1i32, 42i32, 3i32, 4i32];
    let a3_model = seq![50i32, 2i32, 3i32, 4i32];
    proof_assert!(a@ == *a_model);
    proof_assert!(a2@ == *a2_model);
    proof_assert!(a3@ == *a3_model);
    proof_assert!(a4@ == *a_model);
}
