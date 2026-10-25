//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `core::borrow` (the blanket `impl<T> Borrow<T> for T`), verifying the model matches Rust behavior.

use std::borrow::Borrow;

/// Adapted from the example in the documentation of `Borrow::borrow`
/// (<https://doc.rust-lang.org/std/borrow/trait.Borrow.html#tymethod.borrow>), which calls a
/// `check<T: Borrow<str>>` with a `String` and a `&str`. Those calls use the impls
/// `Borrow<str> for String` and `Borrow<T> for &T`, not the blanket impl, and `str` has no Lean
/// model: `check` uses `u32` instead, and is called with a `u32` (the blanket impl).
fn check<T: Borrow<u32>>(s: T) {
    assert_eq!(5, *s.borrow());
}

#[verify::test]
pub fn test_borrow_doc() {
    let s = 5u32;

    check(s);
}

/// Direct call to the blanket implementation.
#[verify::test]
pub fn test_borrow_direct() {
    let x = 3u32;
    let y: &u32 = <u32 as Borrow<u32>>::borrow(&x);
    assert_eq!(*y, 3);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn borrow_doc() {
        test_borrow_doc();
    }

    #[test]
    fn borrow_direct() {
        test_borrow_direct();
    }
}
