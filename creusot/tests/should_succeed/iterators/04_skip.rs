#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::{invariant::inv, *};

mod common;
use common::Iterator;

pub struct Skip<I: Iterator> {
    iter: I,
    n: usize,
}

impl<I> Iterator for Skip<I>
where
    I: Iterator,
{
    type Item = I::Item;

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (^self).n@ == 0 &&
            exists<s: Seq<Self::Item>, i: &mut I> inv(s) && inv(i)
                && s.len() <= self.n@
                && self.iter.produces(s, *i)
                && (forall<i: Int> 0 <= i && i < s.len() ==> s[i].resolve())
                && i.completed()
                && ^i == (^self).iter
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            o.n@ == 0 && visited.len() > 0
            && exists<s: Seq<Self::Item>> inv(s)
                && s.len() == self.n@
                && self.iter.produces(s.concat(visited), o.iter)
                && forall<i: Int> 0 <= i && i < s.len() ==> s[i].resolve()
        }
    }

    #[law]
    #[open]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<I::Item> {
        let old_self = snapshot! { self };
        let mut n = std::mem::take(&mut self.n);
        let mut skipped = snapshot! { Seq::EMPTY };

        #[invariant(inv(self))]
        #[invariant(inv(*skipped))]
        #[invariant(skipped.len() + n@ == old_self.n@)]
        #[invariant(old_self.iter.produces(skipped.inner(), self.iter))]
        #[invariant(forall<i: Int> 0 <= i && i < skipped.len() ==> skipped[i].resolve())]
        #[invariant((*self).n@ == 0)]
        #[invariant(^*old_self == ^self)]
        loop {
            let r = self.iter.next();
            if n == 0 {
                return r;
            }
            if let Some(x) = r {
                skipped = snapshot! { skipped.concat(Seq::singleton(x)) };
                n -= 1
            } else {
                return r;
            }
        }
    }
}
