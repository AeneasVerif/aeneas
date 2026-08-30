//@ [!lean] skip
//@ [lean] known-failure
//! Companion to issue https://github.com/AeneasVerif/aeneas/issues/767
//!
//! A record (braced) struct does not get added to Rust's value namespace. Thus an
//! ordinary function can use the constructor name. Aeneas must not mis-categorize
//! such a function to `<Type>.constructor`. It should only rename a tuple-struct
//! constructor used as a first-class value (see `issue-767-name-clash.rs`).
//!
//! Currently, the type `Foo` and the function `Foo` get the same name, and this gives
//! a name-clash error which suggests a fix using `#[aeneas::rename(...)]` attribute.
pub struct Foo {
    pub x: u32,
}

pub fn Foo() -> u32 {
    0
}

pub fn use_foo() -> u32 {
    Foo()
}
