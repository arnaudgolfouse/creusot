use crate::{
    logic::{FMap, ra::RA},
    *,
};

impl<K, V: RA> RA for FMap<K, V> {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        self.merge(other, |(x, y): (V, V)| x.op(y))
    }

    #[logic]
    #[open]
    fn compatible(self, other: Self) -> bool {
        pearlite! {
            forall<k: K> self.get(k).compatible(other.get(k))
        }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => self.compatible(c) && self.op(c) == other,
        None => forall<c: Self> !(self.compatible(c) && self.op(c) == other),
    })]
    fn incl(self, other: Self) -> Option<Self> {
        let res = self.missing_part(other);
        if self.op(res).ext_eq(other) { Some(res) } else { None }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.compatible(self) && self.op(self) == self))]
    fn idemp(self) -> bool {
        pearlite! {
            forall<k: K> self.get(k).idemp()
        }
    }

    #[law]
    #[open(self)]
    #[requires(a.compatible(b))]
    #[ensures(b.compatible(a))]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        proof_assert!(a.op(b).ext_eq(b.op(a)));
    }

    #[law]
    #[open(self)]
    #[requires(a.compatible(b) && a.op(b).compatible(c))]
    #[ensures(b.compatible(c) && a.compatible(b.op(c)))]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) {
        proof_assert!(a.op(b).op(c).ext_eq(a.op(b.op(c))));
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(b) => b.incl(self) != None && b.idemp() &&
           forall<c: Self> c.incl(self) != None && c.idemp() ==> c.incl(b) != None,
        None => forall<b: Self> ! (b.incl(self) != None && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        let res = self.maximal_idemp_part();
        if res.incl(self) != None { Some(res) } else { None }
    }
}

impl<K, V: RA> FMap<K, V> {
    /// Used in `<FMap as RA>::incl`.
    #[logic]
    #[open]
    pub fn missing_part(self, other: Self) -> Self {
        other.filter_map(|(k, vo)| match self.get(k).incl(Some(vo)) {
            Some(r) => r,
            None => None,
        })
    }

    /// Used in `<FMap as RA>::maximal_idemp`.
    #[logic]
    #[open]
    pub fn maximal_idemp_part(self) -> Self {
        self.filter_map(|(_, v): (K, V)| v.maximal_idemp())
    }
}
