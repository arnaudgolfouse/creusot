extern crate creusot_contracts;
use creusot_contracts::*;

pub fn while_loop_variant(mut x: u32) {
    #[variant(x)]
    while x > 0 {
        x -= 1;
    }
}
