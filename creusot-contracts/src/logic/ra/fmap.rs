use crate::{
    logic::{
        FMap,
        ra::{RA, UnitRA, update::LocalUpdate},
    },
    *,
};

impl<K, V: RA> RA for FMap<K, V> {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        pearlite! {
            if (forall<k: K> self.get(k).op(other.get(k)) != None) {
                Some(self.total_op(other))
            } else {
                None
            }
        }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        pearlite! {
            if (forall<k: K> factor.get(k).incl(self.get(k))) {
                let res = self.filter_map(|(k, vo): (K, V)|
                    match Some(vo).factor(factor.get(k)) {
                        Some(r) => r,
                        None => None,
                });
                proof_assert!(
                    match factor.op(res) {
                        None => false,
                        Some(o) => o.ext_eq(self)
                    }
                );
                Some(res)
            } else {
                None
            }
        }
    }

    #[law]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        proof_assert!(match (a.op(b), b.op(a)) {
            (Some(ab), Some(ba)) => ab.ext_eq(ba),
            (None, None) => true,
            _ => false,
        })
    }

    #[law]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {
        match (a.op(b), b.op(c)) {
            (Some(ab), Some(bc)) => match (ab.op(c), a.op(bc)) {
                (Some(x), Some(y)) => proof_assert!(x.ext_eq(y)),
                _ => (),
            },
            _ => (),
        }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => c.op(c) == Some(c) && c.op(self) == Some(self),
        None => true
    })]
    fn core(self) -> Option<Self> {
        Some(self.core_total())
    }

    #[logic]
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self) {
        let _ = V::core_is_maximal_idemp;
    }
}

impl<K, V: RA> UnitRA for FMap<K, V> {
    #[logic]
    #[open]
    #[ensures(forall<x: Self> #[trigger(x.op(result))] x.op(result) == Some(x))]
    fn unit() -> Self {
        proof_assert!(forall<x: Self> x.op(Self::empty()).unwrap_logic().ext_eq(x));
        Self::empty()
    }

    #[logic]
    #[open]
    #[ensures(result.op(result) == Some(result))]
    #[ensures(result.op(self) == Some(self))]
    fn core_total(self) -> Self {
        let r = self.filter_map(|(_, v): (K, V)| v.core());
        proof_assert!(r.op(r).unwrap_logic().ext_eq(r));
        proof_assert!(r.op(self).unwrap_logic().ext_eq(self));
        r
    }

    #[logic]
    #[ensures(self.core() == Some(self.core_total()))]
    fn core_is_total(self) {}
}

impl<K, V: RA> FMap<K, V> {
    #[logic]
    #[requires(forall<k: K> self.get(k).op(other.get(k)) != None)]
    #[ensures(forall<k: K> Some(result.get(k)) == self.get(k).op(other.get(k)))]
    pub fn total_op(self, other: Self) -> Self {
        self.merge(other, |(x, y): (V, V)| match x.op(y) {
            Some(r) => r,
            _ => such_that(|_| true),
        })
    }
}

pub struct FMapInsertLocalUpdate<K, V>(pub Snapshot<K>, pub Snapshot<V>);

impl<K, V: RA> LocalUpdate<FMap<K, V>> for FMapInsertLocalUpdate<K, V> {
    #[logic]
    #[open]
    fn premise(self, from_auth: FMap<K, V>, _: FMap<K, V>) -> bool {
        from_auth.get(*self.0) == None
    }

    #[logic]
    #[open]
    fn update(self, from_auth: FMap<K, V>, from_frag: FMap<K, V>) -> (FMap<K, V>, FMap<K, V>) {
        (from_auth.insert(*self.0, *self.1), from_frag.insert(*self.0, *self.1))
    }

    #[logic]
    #[allow(unused)]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(
        self,
        from_auth: FMap<K, V>,
        from_frag: FMap<K, V>,
        frame: Option<FMap<K, V>>,
    ) {
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        proof_assert!(match Some(to_frag).op(frame) {
            Some(Some(x)) => to_auth.ext_eq(x),
            _ => false,
        });
    }
}
