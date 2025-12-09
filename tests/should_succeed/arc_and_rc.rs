extern crate creusot_contracts;

use ::std::{rc::Rc, sync::Arc};
use creusot_contracts::prelude::*;

pub fn rc() {
    let rc = Rc::new(1);
    proof_assert!(*rc@ == 1i32);
    let inner = rc.as_ref();
    proof_assert!(inner@ == 1);

    let rc2 = rc.clone();
    proof_assert!(rc == rc2);

    let b = Rc::ptr_eq(&rc, &rc2);
    proof_assert!(b);

    let rc3 = Rc::new(2);
    let b2 = Rc::ptr_eq(&rc, &rc3);
    // the content of the two rc is not the same, so their pointer have to be different
    proof_assert!(!b2);
}

pub fn arc() {
    let arc = Arc::new(2);
    proof_assert!(*arc@ == 2i32);
    let inner = arc.as_ref();
    proof_assert!(inner@ == 2);
}
