//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
#![feature(step_trait)]
//! Tests for `Step::forward_overflowing` / `Step::backward_overflowing`,
//! verifying that the uniform model in `Aeneas.Std.Core.Iter` matches Rust
//! behavior.
//!
//! The standard library implementations depends on whether the scalar width is
//! wider or narrower than `usize` while we use a uniform, equivalent model in Lean.

use core::iter::Step;

// ---------------------------------------------------------------------------
// usize — same width as the count, so `try_from` always succeeds.
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_usize_forward_no_overflow() {
    let (v, o) = Step::forward_overflowing(10usize, 5);
    assert!(v == 15usize);
    assert!(o == false);
}

/// Documented corollary: `forward_overflowing(a, 0) == (a, false)`.
#[verify::test]
pub fn test_usize_forward_zero() {
    let (v, o) = Step::forward_overflowing(7usize, 0);
    assert!(v == 7usize);
    assert!(o == false);
}

#[verify::test]
pub fn test_usize_forward_overflow_wraps_to_zero() {
    let (v, o) = Step::forward_overflowing(usize::MAX, 1);
    assert!(v == 0usize);
    assert!(o == true);
}

#[verify::test]
pub fn test_usize_forward_overflow_max_count() {
    let (v, o) = Step::forward_overflowing(1usize, usize::MAX);
    assert!(v == 0usize);
    assert!(o == true);
}

#[verify::test]
pub fn test_usize_backward_no_overflow() {
    let (v, o) = Step::backward_overflowing(10usize, 5);
    assert!(v == 5usize);
    assert!(o == false);
}

#[verify::test]
pub fn test_usize_backward_overflow() {
    let (v, o) = Step::backward_overflowing(0usize, 1);
    assert!(v == usize::MAX);
    assert!(o == true);
}

// ---------------------------------------------------------------------------
// u8 — narrower than the count, so `u8::try_from(n)` can fail. This is the
// branch that returns `(start.wrapping_add(n as u8), true)`.
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_u8_forward_no_overflow() {
    let (v, o) = Step::forward_overflowing(1u8, 2);
    assert!(v == 3u8);
    assert!(o == false);
}

/// `n` fits in `u8`, but the sum does not: `200 + 100 == 300 == 44 (mod 256)`.
#[verify::test]
pub fn test_u8_forward_overflow_count_fits() {
    let (v, o) = Step::forward_overflowing(200u8, 100);
    assert!(v == 44u8);
    assert!(o == true);
}

/// `n` does *not* fit in `u8`, so `u8::try_from` fails: the value is still
/// `start + n` truncated, and the flag is forced to `true`.
#[verify::test]
pub fn test_u8_forward_count_too_large() {
    let (v, o) = Step::forward_overflowing(0u8, 300);
    assert!(v == 44u8);
    assert!(o == true);
}

#[verify::test]
pub fn test_u8_backward_no_overflow() {
    let (v, o) = Step::backward_overflowing(10u8, 3);
    assert!(v == 7u8);
    assert!(o == false);
}

#[verify::test]
pub fn test_u8_backward_overflow_count_fits() {
    let (v, o) = Step::backward_overflowing(3u8, 5);
    assert!(v == 254u8);
    assert!(o == true);
}

/// `try_from` failure path for the backward direction:
/// `5 - 300 == 217 (mod 256)`.
#[verify::test]
pub fn test_u8_backward_count_too_large() {
    let (v, o) = Step::backward_overflowing(5u8, 300);
    assert!(v == 217u8);
    assert!(o == true);
}

// ---------------------------------------------------------------------------
// i32 — signed, so the std impl uses `overflowing_{add,sub}_unsigned`. Since
// the count is unsigned, `forward` can only overflow above and `backward` only
// below.
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_i32_forward_negative_no_overflow() {
    let (v, o) = Step::forward_overflowing(-5i32, 3);
    assert!(v == -2i32);
    assert!(o == false);
}

#[verify::test]
pub fn test_i32_forward_overflow() {
    let (v, o) = Step::forward_overflowing(i32::MAX, 1);
    assert!(v == i32::MIN);
    assert!(o == true);
}

/// `u32::try_from(usize::MAX)` fails on a 64-bit target and succeeds on a
/// 32-bit one; both paths yield the same answer, which is why the model can be
/// uniform.
#[verify::test]
pub fn test_i32_forward_count_max() {
    let (v, o) = Step::forward_overflowing(0i32, usize::MAX);
    assert!(v == -1i32);
    assert!(o == true);
}

#[verify::test]
pub fn test_i32_backward_negative_no_overflow() {
    let (v, o) = Step::backward_overflowing(-5i32, 3);
    assert!(v == -8i32);
    assert!(o == false);
}

#[verify::test]
pub fn test_i32_backward_overflow() {
    let (v, o) = Step::backward_overflowing(i32::MIN, 1);
    assert!(v == i32::MAX);
    assert!(o == true);
}

#[verify::test]
pub fn test_i32_backward_count_max() {
    let (v, o) = Step::backward_overflowing(0i32, usize::MAX);
    assert!(v == 1i32);
    assert!(o == true);
}

// ---------------------------------------------------------------------------
// i8 — the narrowest signed width, where a count of a few hundred already
// exceeds `u8` and exercises the `try_from` failure path.
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_i8_forward_overflow() {
    let (v, o) = Step::forward_overflowing(120i8, 10);
    assert!(v == -126i8);
    assert!(o == true);
}

#[verify::test]
pub fn test_i8_backward_overflow() {
    let (v, o) = Step::backward_overflowing(-120i8, 10);
    assert!(v == 126i8);
    assert!(o == true);
}

// ---------------------------------------------------------------------------
// u128 / i128 — wider than the count on a 64-bit target, where the std impl
// casts `n` exactly instead of going through `try_from`.
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_u128_forward_no_overflow() {
    let (v, o) = Step::forward_overflowing(1u128, usize::MAX);
    assert!(o == false);
    assert!(v == (usize::MAX as u128) + 1);
}

#[verify::test]
pub fn test_u128_forward_overflow() {
    let (v, o) = Step::forward_overflowing(u128::MAX, 1);
    assert!(v == 0u128);
    assert!(o == true);
}

#[verify::test]
pub fn test_i128_backward_overflow() {
    let (v, o) = Step::backward_overflowing(i128::MIN, 1);
    assert!(v == i128::MAX);
    assert!(o == true);
}
