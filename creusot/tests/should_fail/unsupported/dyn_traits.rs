extern crate creusot_contracts;
use creusot_contracts::*;

#[derive(Debug)]
struct S(i32);

trait Tr {
    #[ensures(true)]
    fn foo(&self);
}

#[ensures(result@ == 1)]
pub fn f(x: &dyn Tr) -> i32 {
    x.foo();
    1
}

fn pass_generics<T: Tr>(x: T) {
    x.foo();
}

pub fn call_generic(x: &dyn Tr) {
    pass_generics(x);
}
