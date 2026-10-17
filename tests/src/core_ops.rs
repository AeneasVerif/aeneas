//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! The `core::ops` arithmetic and bitwise traits on integer types.
//!
//! Using an operator on a concrete integer type compiles to a primitive MIR
//! operation, but code that is generic over the operator traits calls the trait
//! methods, and the trait implementations for the integer types have to be
//! provided by the standard library models.
use core::ops::*;

pub trait Int:
    Copy
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitXor<Output = Self>
    + Shl<u32, Output = Self>
    + Shr<i32, Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
{
}

impl Int for u32 {}
impl Int for i64 {}

pub fn arith<T: Int>(x: T, y: T) -> T {
    ((x + y) - y) * y / y
}

pub fn bits<T: Int>(x: T, y: T) -> T {
    (x & y) | (x ^ y)
}

pub fn shifts<T: Int>(x: T) -> T {
    (x << 3u32) >> 1i32
}

pub fn assigns<T: Int>(mut x: T, y: T) -> T {
    x += y;
    x -= y;
    x *= y;
    x /= y;
    x &= y;
    x ^= y;
    x |= y;
    x
}

/// Calling the trait methods directly.
pub fn direct(x: u32, s: u8) -> u32 {
    <u32 as Shl<u8>>::shl(<u32 as Add>::add(x, 1), s)
}

#[verify::test]
pub fn test_arith() {
    assert!(arith(7u32, 2u32) == 7);
    assert!(arith(-7i64, 2i64) == -7);
}

#[verify::test]
pub fn test_bits() {
    assert!(bits(12u32, 10u32) == 14);
    assert!(bits(12i64, 10i64) == 14);
}

#[verify::test]
pub fn test_shifts() {
    assert!(shifts(5u32) == 20);
    assert!(shifts(-5i64) == -20);
}

#[verify::test]
pub fn test_assigns() {
    assert!(assigns(7u32, 3u32) == 3);
    assert!(assigns(7i64, 3i64) == 3);
}

#[verify::test]
pub fn test_direct() {
    assert!(direct(2, 3) == 24);
}
