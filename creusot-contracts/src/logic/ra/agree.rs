use crate::{logic::ra::RA, *};

/// The 'agreement' Resource Algebra.
///
/// This has the property that all resource with the same id have the same value
/// (they 'agree').
pub struct Ag<T>(pub T);

impl<T> RA for Ag<T> {
    #[logic]
    #[open]
    fn op(self, _: Self) -> Self {
        self
    }

    #[logic]
    #[open]
    fn compatible(self, other: Self) -> bool {
        self == other
    }

    #[logic]
    #[open]
    #[ensures(result == self.compatible(self) && (self.op(self) == self))]
    fn idemp(self) -> bool {
        true
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => self.compatible(c) && self.op(c) == other,
        None => forall<c: Self> !(self.compatible(c) && self.op(c) == other),
    })]
    fn incl(self, other: Self) -> Option<Self> {
        if self == other { Some(self) } else { None }
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
        Some(self)
    }
}
