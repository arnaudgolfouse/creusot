// WHY3PROVE
#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{
    invariant::{Invariant, inv},
    logic::Mapping,
    *,
};

mod common;
use common::Iterator;

#[derive(Resolve)]
pub struct Filter<I: Iterator, F: FnMut(&I::Item) -> bool> {
    pub iter: I,
    pub func: F,
}

impl<I: Iterator, F: FnMut(&I::Item) -> bool> Invariant for Filter<I, F> {
    #[logic(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            // trivial precondition: simplification for sake of proof complexity
            forall<f: F, i: &I::Item> f.precondition((i,)) &&
            // immutable state: simplification for sake of proof complexity
            (forall<f: F, g: F> f.hist_inv(g) ==> f == g) &&
            // precision of postcondition. In some sense this is not *necessary*, but without this we cannot prove that we return *all* elements
            // for all elements where the predicate evaluated to true, since we don't actually have access to the closure's return value directly,
            // only what the postcondition says about it.
            (forall<f1: F, f2: F, i> !(f1.postcondition_mut((i,), f2, true) && f1.postcondition_mut((i,), f2, false)))
        }
    }
}

impl<I: Iterator, F: FnMut(&I::Item) -> bool> Iterator for Filter<I, F> {
    type Item = I::Item;

    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (exists<s: Seq<_>, e: &mut I > self.iter.produces(s, *e) && e.completed() &&
                forall<i> 0 <= i && i < s.len() ==> (*self).func.postcondition_mut((&s[i],), (^self).func, false))
            && (*self).func == (^self).func
        }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[open]
    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.invariant() ==>
            self.func.hist_inv(succ.func) &&
            // f here is a mapping from indices of `visited` to those of `s`, where `s` is the whole sequence produced by the underlying iterator
            // Interestingly, Z3 guesses `f` quite readily but gives up *totally* on `s`. However, the addition of the final assertions on the correctness of the values
            // blocks z3's guess for `f`.
            exists<s: Seq<Self::Item>, f: Mapping<Int, Int>> self.iter.produces(s, succ.iter) &&
                // F is a monotone mapping
                (forall<i, j> 0 <= i && i <= j && j < visited.len() ==> 0 <= f.get(i) && f.get(i) <= f.get(j) && f.get(j) < s.len()) &&
                (forall<i> 0 <= i && i < visited.len() ==> visited[i] == s[f.get(i)]) &&

                (forall<i> 0 <= i &&  i < s.len() ==>
                    (exists<j> 0 <= j && j < visited.len() && f.get(j) == i) == self.func.postcondition_mut((&s[i],), self.func, true)
                )
        }
    }

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<I::Item> {
        let old_self = snapshot! { self};
        let mut produced = snapshot! { Seq::empty() };

        #[invariant(inv(self))]
        #[invariant(self.func == old_self.func)]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==> self.func.postcondition_mut((&produced[i],), self.func, false))]
        #[invariant(old_self.iter.produces(*produced, self.iter))]
        #[invariant(old_self.func.hist_inv(self.func))]
        while let Some(n) = self.iter.next() {
            produced = snapshot! { produced.push_back(n) };
            proof_assert!(old_self.iter.produces(*produced, self.iter));
            if (self.func)(&n) {
                return Some(n);
            }
        }

        None
    }
}

#[pure]
#[requires(immutable(f))]
#[requires(no_precondition(f))]
#[requires(precise(f))]
#[ensures(result.iter == iter && result.func == f)]
pub fn filter<I: Iterator, P>(iter: I, f: P) -> Filter<I, P>
where
    P: for<'a> FnMut(&I::Item) -> bool,
{
    Filter { iter, func: f }
}

#[ensures(forall< i> 0 <= i && i < result@.len() ==> result[i] < n)]
#[ensures(forall< i> 0 <= i && i < result@.len() ==> v@.contains(result[i]))]
pub fn less_than(v: Vec<u32>, n: u32) -> Vec<u32> {
    v.into_iter()
        .filter(
            #[ensures(result == (*i < n))]
            |i| *i < n,
        )
        .collect()
}

#[open]
#[logic(prophetic)]
pub fn no_precondition<A, F: FnMut(A) -> bool>(_: F) -> bool {
    pearlite! { forall<f: F, i: A> f.precondition((i,)) }
}

#[open]
#[logic(prophetic)]
pub fn immutable<A, F: FnMut(A) -> bool>(_: F) -> bool {
    pearlite! { forall<f: F, g: F> f.hist_inv(g) ==> f == g }
}

#[open]
#[logic(prophetic)]
pub fn precise<A, F: FnMut(A) -> bool>(_: F) -> bool {
    pearlite! { forall<f1: F, f2: F, i> !(f1.postcondition_mut((i,), f2, true) && f1.postcondition_mut((i,), f2, false)) }
}
