extern crate creusot_contracts;
use creusot_contracts::{logic::*, *};

#[logic]
fn x<T>(v: &Vec<T>) -> Int {
    pearlite! { v.len()@ }
}

pub fn y() {
    let _ = x(&Vec::<()>::new());
}
