//@ [lean] known-failure
//@ [!lean] skip
//@ charon-args=--include=core::mem::swap
//! Checks that a function with a body cannot be mapped to a model, even when it
//! belongs to another crate: `core::mem::swap` has a model which ships with
//! Aeneas, and Charon translates its body because of `--include`.

pub fn f(x: &mut u32, y: &mut u32) {
    core::mem::swap(x, y)
}
