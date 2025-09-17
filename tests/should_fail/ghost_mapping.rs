extern crate creusot_contracts;
use creusot_contracts::{logic::Mapping, *};

#[logic(open(self), prophetic)]
pub fn f(x: &mut i32) -> Mapping<(), i32> {
    pearlite! { |_| ^x }
}

#[logic(open(self))]
pub fn g(x: &mut i32) -> Mapping<(), i32> {
    pearlite! { |_| ^x }
}

#[logic(open(self), prophetic)]
pub fn h(y: &mut i32) -> bool {
    pearlite! { forall<_x:Int> ^y == 1i32 }
}

#[logic(open(self))]
pub fn i(y: &mut i32) -> bool {
    pearlite! { forall<_x:Int> ^y == 1i32 }
}
