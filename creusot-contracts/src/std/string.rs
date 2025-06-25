use crate::*;
use ::std::ops::Deref;

extern_spec! {
    mod std {
        mod string {
            impl Deref for String {
                #[pure]
                #[ensures(result@ == self@)]
                fn deref(&self) -> &str;
            }

            impl String {
                #[pure]
                #[ensures(result@ == self@.to_bytes().len())]
                fn len(&self) -> usize;

                #[pure]
                #[requires(exists<s: Seq<char>> s.to_bytes() == bytes@)]
                #[ensures(result@.to_bytes() == bytes@)]
                unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> String;
            }
        }
    }
}

extern_spec! {
    impl str {
        #[pure]
        #[ensures(result@ == self@.to_bytes().len())]
        fn len(&self) -> usize;

        #[terminates] // can OOM (?)
        #[ensures(result@ == self@)]
        fn to_string(&self) -> String;

        #[pure]
        #[requires(exists<i0> 0 <= i0 && i0 <= self@.len() && self@.subsequence(0, i0).to_bytes().len() == ix@)]
        #[ensures(result.0@.concat(result.1@) == self@)]
        #[ensures(result.0@.to_bytes().len() == ix@)]
        fn split_at(&self, ix: usize) -> (&str, &str);
    }
}

impl Seq<char> {
    #[logic]
    #[open]
    pub fn to_bytes(self) -> Seq<u8> {
        pearlite! { self.flat_map(|c: char| c.to_utf8()) }
    }
}

#[trusted]
#[logic]
#[open]
#[ensures(forall<s1: Seq<char>, s2: Seq<char>> s1.to_bytes() == s2.to_bytes() ==> s1 == s2)]
pub fn injective_to_bytes() {}
