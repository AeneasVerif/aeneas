//@ [!lean] skip
//! Test: a variable shadowed by a namespace with the same name.
//!
//! A Rust module `cshadow` becomes the Lean namespace `cshadow`. If a function
//! binds a variable also called `cshadow`, then `cshadow.f` is parsed as a
//! projection out of the variable instead of a reference to the qualified
//! constant, and elaboration fails. The variable must hence be renamed.

pub mod cshadow {
    pub fn f(x: usize) -> usize {
        x
    }

    pub fn g(cshadow: usize) -> usize {
        f(cshadow)
    }
}
