use crate::logic::ra::*;

impl<T> RA for Option<T>
where
    T: RA,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (None, _) => other,
            (_, None) => self,
            (Some(x), Some(y)) => Some(x.op(y)),
        }
    }

    #[logic]
    #[open]
    fn compatible(self, other: Self) -> bool {
        match (self, other) {
            (Some(x), Some(y)) => x.compatible(y),
            _ => true,
        }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => self.compatible(c) && self.op(c) == other,
        None => forall<c: Self> !(self.compatible(c) && self.op(c) == other),
    })]
    fn incl(self, other: Self) -> Option<Self> {
        match (self, other) {
            (None, x) => Some(x),
            (_, None) => None,
            (Some(x), Some(y)) => match x.incl(y) {
                Some(z) => Some(Some(z)),
                None => {
                    if x == y {
                        Some(None)
                    } else {
                        None
                    }
                }
            },
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.compatible(self) && self.op(self) == self))]
    fn idemp(self) -> bool {
        match self {
            None => true,
            Some(x) => x.idemp(),
        }
    }
    #[law]
    #[open(self)]
    #[requires(a.compatible(b))]
    #[ensures(b.compatible(a))]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        let _ = <T as RA>::commutative;
    }

    #[law]
    #[open(self)]
    #[requires(a.compatible(b) && a.op(b).compatible(c))]
    #[ensures(b.compatible(c) && a.compatible(b.op(c)))]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) {
        pearlite! {
            match (a, b, c) {
                (None, _, _) => {},
                (_, None, _) => {},
                (_, _, None) => {},
                (Some(aa), Some(bb), Some(cc)) => {
                    <T as RA>::associative(aa, bb, cc)
                }
            }
        }
    }

    #[logic]
    #[open(self)]
    #[ensures(match result {
        Some(b) => b.incl(self) != None && b.idemp() &&
           forall<c: Self> c.incl(self) != None && c.idemp() ==> c.incl(b) != None,
        None => forall<b: Self> ! (b.incl(self) != None && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        pearlite! {
            match self {
                None => Some(None),
                Some(x) => {
                    match x.maximal_idemp() {
                        None => Some(None),
                        Some(y) => Some(Some(y)),
                    }
                }
            }
        }
    }
}
