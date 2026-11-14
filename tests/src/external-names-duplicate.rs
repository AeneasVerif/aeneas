//@ [lean] known-failure
//@ [!lean] skip
//@ charon-args=--opaque=external_names_duplicate::f
//@ [lean] aeneas-args=-external-names tests/external-names/external-names-duplicate.json
//! Checks that a list of external names which maps the same Rust pattern twice
//! is refused rather than silently picking one of the entries.

fn f(x: u32) -> u32 {
    x
}

pub fn g(x: u32) -> u32 {
    f(x)
}
