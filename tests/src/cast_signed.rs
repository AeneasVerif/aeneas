//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `<uN>::cast_signed` / `<iN>::cast_unsigned`, verifying the
//! bit-pattern-preserving model matches Rust behavior, for every width.

/// `u8::cast_signed`: all-ones reinterprets as -1.
#[verify::test]
pub fn test_u8_cast_signed_all_ones() {
    let x: u8 = 0xFF;
    let y: i8 = x.cast_signed();
    assert!(y == -1i8);
}

/// `i8::cast_unsigned`: -1 reinterprets as 0xFF.
#[verify::test]
pub fn test_i8_cast_unsigned_neg_one() {
    let x: i8 = -1;
    let y: u8 = x.cast_unsigned();
    assert!(y == 0xFFu8);
}

/// `u16::cast_signed`: high-bit-set reinterprets as i16::MIN.
#[verify::test]
pub fn test_u16_cast_signed_high_bit() {
    let x: u16 = 0x8000;
    let y: i16 = x.cast_signed();
    assert!(y == i16::MIN);
}

/// `i16::cast_unsigned`: -1 reinterprets as u16::MAX.
#[verify::test]
pub fn test_i16_cast_unsigned_neg_one() {
    let x: i16 = -1;
    let y: u16 = x.cast_unsigned();
    assert!(y == u16::MAX);
}

/// `u32::cast_signed`: small values are unchanged.
#[verify::test]
pub fn test_u32_cast_signed_small() {
    let x: u32 = 255;
    let y: i32 = x.cast_signed();
    assert!(y == 255i32);
}

/// `u32::cast_signed`: the all-ones pattern reinterprets as -1.
#[verify::test]
pub fn test_u32_cast_signed_all_ones() {
    let x: u32 = 0xFFFFFFFF;
    let y: i32 = x.cast_signed();
    assert!(y == -1i32);
}

/// `u32::cast_signed`: the high-bit-set pattern reinterprets as i32::MIN.
#[verify::test]
pub fn test_u32_cast_signed_high_bit() {
    let x: u32 = 0x80000000;
    let y: i32 = x.cast_signed();
    assert!(y == i32::MIN);
}

/// `i32::cast_unsigned`: -1 reinterprets as the all-ones pattern.
#[verify::test]
pub fn test_i32_cast_unsigned_neg_one() {
    let x: i32 = -1;
    let y: u32 = x.cast_unsigned();
    assert!(y == 0xFFFFFFFFu32);
}

/// `i32::cast_unsigned`: round-trips with `cast_signed`.
#[verify::test]
pub fn test_i32_cast_roundtrip() {
    let x: u32 = 0xDEADBEEF;
    let y: u32 = x.cast_signed().cast_unsigned();
    assert!(y == x);
}

/// `u64::cast_signed`: all-ones reinterprets as -1.
#[verify::test]
pub fn test_u64_cast_signed_all_ones() {
    let x: u64 = u64::MAX;
    let y: i64 = x.cast_signed();
    assert!(y == -1i64);
}

/// `i64::cast_unsigned`: -1 reinterprets as u64::MAX.
#[verify::test]
pub fn test_i64_cast_unsigned_neg_one() {
    let x: i64 = -1;
    let y: u64 = x.cast_unsigned();
    assert!(y == u64::MAX);
}

/// `u128::cast_signed`: the all-ones pattern reinterprets as -1.
#[verify::test]
pub fn test_u128_cast_signed_all_ones() {
    let x: u128 = u128::MAX;
    let y: i128 = x.cast_signed();
    assert!(y == -1i128);
}

/// `i128::cast_unsigned`: -1 reinterprets as u128::MAX.
#[verify::test]
pub fn test_i128_cast_unsigned_neg_one() {
    let x: i128 = -1;
    let y: u128 = x.cast_unsigned();
    assert!(y == u128::MAX);
}

/// `usize::cast_signed`: -1 round-trips through `isize::cast_unsigned`.
#[verify::test]
pub fn test_usize_cast_roundtrip() {
    let x: usize = 12345;
    let y: usize = x.cast_signed().cast_unsigned();
    assert!(y == x);
}

/// `isize::cast_unsigned`: -1 reinterprets as usize::MAX.
#[verify::test]
pub fn test_isize_cast_unsigned_neg_one() {
    let x: isize = -1;
    let y: usize = x.cast_unsigned();
    assert!(y == usize::MAX);
}
