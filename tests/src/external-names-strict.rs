//@ [lean] known-failure
//@ [!lean] skip
//@ [lean] aeneas-args=-warnings-as-errors -external-names tests/external-names/external-names-skipped.json
//! Checks that under `-warnings-as-errors`, an entry of a list of external names
//! which would be skipped with a warning (here, a function entry without
//! `rust_pattern`) is an error instead.

pub fn f(x: u32) -> u32 {
    x
}
