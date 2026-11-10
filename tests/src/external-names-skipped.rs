//@ [!lean] skip
//@ [lean] aeneas-args=-external-names tests/external-names/external-names-skipped.json -extra-includes=ExternalNamesModel
//! Entries of a list of external names which are skipped, or completed, with a
//! warning rather than an error: a function entry without `rust_pattern`, a
//! trait entry whose pattern does not parse (with the method it lists), and an
//! enumeration whose entry leaves out the variant `Nan`, which gets the name it
//! would have without the `body`.

use core::num::FpCategory;

pub fn is_nan(c: FpCategory) -> bool {
    match c {
        FpCategory::Nan => true,
        _ => false,
    }
}
