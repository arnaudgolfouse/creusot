extern crate creusot_contracts;
use creusot_contracts::{logic::ra::Excl, resource::Resource, *};

#[ensures(x.id() != y.id())]
#[ensures(*x == ^x)]
pub fn exclusivity(x: &mut Resource<Excl<i32>>, y: &Resource<Excl<i32>>) {
    if x.id_ghost() == y.id_ghost() {
        x.disjoint_compatible(y);
        assert!(false); // x cannot be compatible with y
    }
}
