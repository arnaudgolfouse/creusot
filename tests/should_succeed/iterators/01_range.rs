#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::{invariant::inv, logic::Seq, *};

mod common;
use common::Iterator;

struct Range {
    pub start: isize,
    pub end: isize,
}

impl Iterator for Range {
    type Item = isize;

    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.resolve() && self.start >= self.end
        }
    }

    #[open]
    #[logic]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.end == o.end && self.start <= o.start
            && (visited.len() > 0 ==> o.start <= o.end)
            && visited.len() == o.start@ - self.start@
            && forall<i> 0 <= i && i < visited.len() ==>
                visited[i]@ == self.start@ + i
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

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<isize> {
        if self.start >= self.end {
            None
        } else {
            let r = self.start;
            self.start += 1;
            Some(r)
        }
    }
}

impl Range {
    #[ensures(result == self)]
    pub fn into_iter(self) -> Self {
        self
    }
}

#[requires(n@ >= 0)]
#[ensures(result == n)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    let mut it = Range { start: 0, end: n }.into_iter();
    let iter_old = snapshot! { it };
    let mut produced = snapshot! { Seq::empty() };
    #[invariant(inv(it))]
    #[invariant(iter_old.produces(produced.inner(), it))]
    #[invariant(i@ == produced.len() && i <= n)]
    loop {
        match it.next() {
            Some(x) => {
                produced = snapshot! { produced.concat(Seq::singleton(x)) };
                i += 1
            }
            None => break,
        }
    }
    i
}
