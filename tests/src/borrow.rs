//@ [!lean] skip
//@ [lean] subdir=Borrow
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean model of the blanket `impl<T> Borrow<T> for T` (`core::borrow`).
//!
//! `check` adapts the example of the documentation of `Borrow::borrow`
//! (<https://doc.rust-lang.org/std/borrow/trait.Borrow.html#tymethod.borrow>).

use std::borrow::Borrow;

/// The doc example calls a `check<T: Borrow<str>>` with a `String` and a `&str`: those calls use
/// the impls `Borrow<str> for String` and `Borrow<T> for &T`, not the blanket impl, and `str` has
/// no Lean model. Here `check` uses `u32` instead, is called with a `u32` (the blanket impl), and
/// returns the borrowed value instead of asserting on it.
pub fn check<T: Borrow<u32>>(s: T) -> u32 {
    *s.borrow()
}

#[verify::test]
pub fn test_check() {
    assert_eq!(check(5u32), 5);
}

/// A direct call of the blanket implementation.
pub fn direct(x: u32) -> u32 {
    *<u32 as Borrow<u32>>::borrow(&x)
}

#[verify::test]
pub fn test_direct() {
    assert_eq!(direct(3), 3);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn borrow() {
        test_check();
        test_direct();
    }
}
