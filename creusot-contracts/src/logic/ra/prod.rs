use crate::{logic::ra::RA, *};

impl<T, U> RA for (T, U)
where
    T: RA,
    U: RA,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        (self.0.op(other.0), self.1.op(other.1))
    }

    #[logic]
    #[open]
    fn compatible(self, other: Self) -> bool {
        self.0.compatible(other.0) && self.1.compatible(other.1)
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => self.compatible(c) && self.op(c) == other,
        None => forall<c: Self> !(self.compatible(c) && self.op(c) == other),
    })]
    fn incl(self, other: Self) -> Option<Self> {
        match (self.0.incl(other.0), self.1.incl(other.1)) {
            (Some(x), Some(y)) => Some((x, y)),
            _ => None,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.compatible(self) && self.op(self) == self))]
    fn idemp(self) -> bool {
        self.0.idemp() && self.1.idemp()
    }

    #[law]
    #[open(self)]
    #[requires(a.compatible(b))]
    #[ensures(b.compatible(a))]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[open(self)]
    #[requires(a.compatible(b) && a.op(b).compatible(c))]
    #[ensures(b.compatible(c) && a.compatible(b.op(c)))]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic]
    #[open(self)]
    #[ensures(match result {
        Some(b) => b.incl(self) != None && b.idemp() &&
           forall<c: Self> c.incl(self) != None && c.idemp() ==> c.incl(b) != None,
        None => forall<b: Self> ! (b.incl(self) != None && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        match (self.0.maximal_idemp(), self.1.maximal_idemp()) {
            (Some(x), Some(y)) => Some((x, y)),
            _ => None,
        }
    }
}
