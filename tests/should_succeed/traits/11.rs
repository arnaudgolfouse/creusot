extern crate creusot_contracts;

use creusot_contracts::*;

#[logic(open)]
pub fn id<T>(x: T) -> T {
    x
}

pub trait A {
    type T;

    #[ensures(id(x) == x)]
    fn f(x: Self::T);
}

pub fn test<T: A>(_: T) {}
