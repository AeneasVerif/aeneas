//@ [!lean] skip
//@ [lean] subdir=UintDivOps
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of division operations on unsigned integers (`div_ceil`).
//!
//! The tests of `ceil_u8`, …, `ceil_usize` start with the example of the documentation of
//! `div_ceil` (<https://doc.rust-lang.org/std/primitive.usize.html#method.div_ceil>), which is the
//! same for every unsigned type.

pub fn ceil_u8(x: u8, y: u8) -> u8 {
    x.div_ceil(y)
}

#[verify::test]
pub fn test_ceil_u8() {
    assert_eq!(ceil_u8(7, 4), 2);
    assert_eq!(ceil_u8(0, 7), 0);
    assert_eq!(ceil_u8(9, 3), 3);
    assert_eq!(ceil_u8(255, 1), 255);
    assert_eq!(ceil_u8(255, 2), 128);
    assert_eq!(ceil_u8(255, 255), 1);
    assert_eq!(ceil_u8(254, 255), 1);
}

pub fn ceil_u16(x: u16, y: u16) -> u16 {
    x.div_ceil(y)
}

#[verify::test]
pub fn test_ceil_u16() {
    assert_eq!(ceil_u16(7, 4), 2);
}

pub fn ceil_u32(x: u32, y: u32) -> u32 {
    x.div_ceil(y)
}

#[verify::test]
pub fn test_ceil_u32() {
    assert_eq!(ceil_u32(7, 4), 2);
}

pub fn ceil_u64(x: u64, y: u64) -> u64 {
    x.div_ceil(y)
}

#[verify::test]
pub fn test_ceil_u64() {
    assert_eq!(ceil_u64(7, 4), 2);
}

pub fn ceil_u128(x: u128, y: u128) -> u128 {
    x.div_ceil(y)
}

#[verify::test]
pub fn test_ceil_u128() {
    assert_eq!(ceil_u128(7, 4), 2);
}

pub fn ceil_usize(x: usize, y: usize) -> usize {
    x.div_ceil(y)
}

/// Edge cases: no overflow near `MAX`.
#[verify::test]
pub fn test_ceil_usize() {
    assert_eq!(ceil_usize(7, 4), 2);
    assert_eq!(ceil_usize(usize::MAX, 1), usize::MAX);
    // Not inlined in `assert_eq!`: rustc would promote it to a constant using an unchecked
    // division, which Aeneas extracts to the missing `Usize.div`.
    let half = usize::MAX / 2 + 1;
    assert_eq!(ceil_usize(usize::MAX, 2), half);
    assert_eq!(ceil_usize(usize::MAX, usize::MAX), 1);
    assert_eq!(ceil_usize(usize::MAX - 1, usize::MAX), 1);
}

/// The number of chunks of size `chunk` needed to hold `len` elements.
pub fn num_chunks(len: usize, chunk: usize) -> usize {
    len.div_ceil(chunk)
}

#[verify::test]
pub fn test_num_chunks() {
    assert_eq!(num_chunks(10, 3), 4);
    assert_eq!(num_chunks(9, 3), 3);
    assert_eq!(num_chunks(0, 5), 0);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uint_div_ops() {
        test_ceil_u8();
        test_ceil_u16();
        test_ceil_u32();
        test_ceil_u64();
        test_ceil_u128();
        test_ceil_usize();
        test_num_chunks();
    }
}
