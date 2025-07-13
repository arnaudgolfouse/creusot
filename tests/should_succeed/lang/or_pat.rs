extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
#[ensures(x == (None, None) ==> result == 1i32)]
pub fn f(x: (Option<i32>, Option<i32>)) -> i32 {
    match x {
        (Some(x), None) | (None, Some(x)) => x,
        _ => 1i32,
    }
}
