extern crate creusot_contracts;
use creusot_contracts::*;

pub trait BadLaw {
    #[law]
    fn my_law<T>(x: T);
}

impl BadLaw for () {
    fn my_law<T>(_: T) {}
}
