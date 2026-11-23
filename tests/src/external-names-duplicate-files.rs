//@ [lean] known-failure
//@ [!lean] skip
//@ [lean] aeneas-args=-external-names tests/external-names/external-names.json -external-names tests/external-names/external-names.json
//! Checks that two files cannot map the same pattern: here, the same file is
//! given twice.

pub fn f() {}
