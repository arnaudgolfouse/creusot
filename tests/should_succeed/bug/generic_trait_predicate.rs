extern crate creusot_contracts;

use creusot_contracts::*;

pub trait CP {
    #[logic(open)]
    fn match_t<K>() -> bool {
        pearlite! { Self::match_n::<K>() }
    }

    #[logic]
    fn match_n<K>() -> bool;
}

impl<L, R> CP for (L, R) {
    #[logic(open)]
    fn match_n<N>() -> bool {
        pearlite! { true }
    }
}
