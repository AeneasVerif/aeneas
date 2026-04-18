//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for miscellaneous core stdlib items: `core::hint::black_box`,
//! `core::borrow::Borrow`, and scalar `core::cmp::Eq` impls.

use core::hint::black_box;

/// `core::hint::black_box` — adapted from docs (docs use asm/intrinsics).
/// Semantically it's the identity function at the value level, so we just
/// verify that.
#[verify::test]
pub fn test_black_box_identity() {
    let y = black_box(97u32);
    assert!(y == 97);
}

/// `Borrow<T> for &T::borrow` — identity on references. In Rust the method
/// is called implicitly; in Aeneas we exercise it by converting `&u32` to a
/// position where Borrow is needed. For this test we just verify `borrow()`
/// on a reference yields an equivalent reference.
use core::borrow::Borrow;

#[verify::test]
pub fn test_borrow_ref() {
    let x: u32 = 42;
    let r: &u32 = &x;
    let b: &u32 = r.borrow();
    assert!(*b == 42);
}

/// `Eq for u8::assert_receiver_is_total_eq` and `Eq for usize::...` are
/// marker methods auto-invoked when `#[derive(Eq)]` is used on a struct
/// containing the scalar. Here we trigger them by deriving `Eq` on a small
/// struct. Rust's compile-time check invokes `assert_receiver_is_total_eq`.
#[derive(PartialEq, Eq)]
pub struct ByteHolder { b: u8 }

#[derive(PartialEq, Eq)]
pub struct SizeHolder { s: usize }

#[verify::test]
pub fn test_eq_u8_via_derive() {
    let a = ByteHolder { b: 5 };
    let b = ByteHolder { b: 5 };
    assert!(a == b);
}

#[verify::test]
pub fn test_eq_usize_via_derive() {
    let a = SizeHolder { s: 5 };
    let b = SizeHolder { s: 5 };
    assert!(a == b);
}
