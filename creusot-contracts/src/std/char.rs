use crate::{Default, *};
pub use ::std::char::*;

impl View for char {
    type ViewTy = Int;
    #[logic]
    #[trusted]
    #[creusot::builtins = "creusot.prelude.Char.to_int"]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl DeepModel for char {
    type DeepModelTy = Int;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self@ }
    }
}

impl Default for char {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        pearlite! { self@ == 0 }
    }
}

/// Extra methods for `char`
pub trait CharExt {
    #[logic]
    pub fn to_utf8(self) -> Seq<u8>;
}

impl CharExt for char {
    #[logic]
    #[trusted]
    #[ensures(1 <= result.len() && result.len() <= 4)]
    fn to_utf8(self) -> Seq<u8> {
        dead
    }
}

#[trusted]
#[logic]
#[open]
#[ensures(forall<c1: char, c2: char> c1.to_utf8() == c2.to_utf8() ==> c1 == c2)]
pub fn injective_to_utf8() {}
