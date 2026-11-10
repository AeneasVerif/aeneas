//@ charon-args=--opaque=external_names::is_mult
//@ aeneas-args=-external-names tests/external-names/external-names.json -extra-includes=ExternalNamesModel
//@[!lean] skip
//! This file checks that a list of external names given through
//! `-external-names` is read, and that its entries are used.

fn is_mult(x: u32, y: u32) -> bool {
    x % y == 0
}

fn use_is_mult(x: u32) -> bool {
    is_mult(x, 3)
}
