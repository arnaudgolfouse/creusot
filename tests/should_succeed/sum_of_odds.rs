// Toy example testing the lemma function feature of Creusot

extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

#[logic]
fn sqr(x: Int) -> Int {
    x * x
}

#[logic]
fn is_square(y: Int) -> bool {
    pearlite! { exists<z> y == sqr(z) }
}

#[logic]
#[variant(x)]
fn sum_of_odd(x: Int) -> Int {
    if x <= 0 { 0 } else { sum_of_odd(x - 1) + 2 * x - 1 }
}

#[logic]
#[requires(x >= 0)]
#[ensures(sum_of_odd(x) == sqr(x))]
#[variant(x)]
fn sum_of_odd_is_sqr(x: Int) {
    pearlite! { if x > 0 { sum_of_odd_is_sqr(x-1) } else { () } }
}

#[requires(x@ < 0x10000)]
#[ensures(result@ == sum_of_odd(x@))]
fn compute_sum_of_odd(x: u32) -> u32 {
    let mut s: u32 = 0;
    #[invariant(s@ == sum_of_odd(produced.len()))]
    for i in 0..x {
        proof_assert! {
            sum_of_odd_is_sqr(i@);
            true
        };
        s += 2 * i + 1;
    }
    return s;
}

#[requires(x@ < 0x10000)]
pub fn test(x: u32) {
    let y = compute_sum_of_odd(x);
    proof_assert! {
        sum_of_odd_is_sqr(x@);
        is_square(y@)
    }
}
