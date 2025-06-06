use crate::{
    logic::ra::{RA, excl::Excl},
    *,
};

/// The relation used in [`View`].
pub trait ViewRel {
    /// The type of the _authority_ portion of a view
    type Auth;
    /// The type of a _fragment_ portion of a view
    type Frag: RA;

    /// The relation between the authority and a fragment
    #[logic]
    fn rel(a: Self::Auth, f: Self::Frag) -> bool;

    #[law]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1) != None)]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Self::Auth, f1: Self::Frag, f2: Self::Frag);
}

/// The 'view' Resource Algebra.
///
/// This resource is parametrized by a [relation](ViewRel) `R` between an
/// **authoritative** part (of type `R::Auth`) and a **fragment** part
/// (of type `R::Frag`).
///
/// The authoritative part is unique, while the fragment part might not be. When the
/// two are present, the relation between the two must hold.
// NOTE: we could add (discardable) fragments for the auth part
pub struct View<R>
where
    R: ViewRel,
{
    /// Authoritative part of the view
    ///
    /// Note the [`Excl`], which guarantees that only one
    /// [`Resource`](crate::resource::Resource) wrapping a [`View`] may have the
    /// authoritative part.
    pub auth: Option<Excl<R::Auth>>,
    /// Fragment part of the view
    pub frag: Option<R::Frag>,
}

impl<R> View<R>
where
    R: ViewRel,
{
    /// Create a new `View` containing an authoritative version of `x`.
    #[logic]
    #[open]
    pub fn mkauth(a: R::Auth) -> Self {
        Self { auth: Some(Excl(a)), frag: None }
    }

    /// Create a new `View` containing a fragment version of `x`.
    #[logic]
    #[open]
    pub fn mkfrag(f: R::Frag) -> Self {
        Self { auth: None, frag: Some(f) }
    }
}

impl<R> RA for View<R>
where
    R: ViewRel,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        let (auth, frag) = (self.auth, self.frag).op((other.auth, other.frag));
        Self { auth, frag }
    }

    #[logic]
    #[open]
    fn compatible(self, other: Self) -> bool {
        (self.auth, self.frag).compatible((other.auth, other.frag))
            && match (self.auth.op(other.auth), self.frag.op(other.frag)) {
                (Some(Excl(auth)), Some(frag)) => R::rel(auth, frag),
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
        match (self.auth, self.frag).incl((other.auth, other.frag)) {
            Some((auth, frag)) => {
                let res = Self { auth, frag };
                if self.compatible(res) { Some(res) } else { None }
            }
            None => None,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.compatible(self) && self.op(self) == self))]
    fn idemp(self) -> bool {
        (self.auth, self.frag).idemp()
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
    #[ensures(a.compatible(b.op(c)) && b.compatible(c))]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) {
        match (b.auth.op(c.auth), b.frag.op(c.frag)) {
            (Some(Excl(_)), Some(_)) => {
                proof_assert!(a.auth == None);
            }
            _ => {}
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
        match (self.auth.maximal_idemp(), self.frag.maximal_idemp()) {
            (Some(auth), Some(frag)) => {
                let self_valid = match (self.auth, self.frag) {
                    (Some(Excl(a)), Some(f)) => R::rel(a, f),
                    _ => true,
                };
                if self_valid { Some(Self { auth, frag }) } else { None }
            }
            _ => None,
        }
    }
}
