#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[check(terminates)]
fn terminates_while_loop() {
    #[allow(while_true)]
    while true {}
}

#[check(terminates)]
fn terminates_loop_loop() {
    loop {}
}
