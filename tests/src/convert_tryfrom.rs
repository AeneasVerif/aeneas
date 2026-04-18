//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `TryFrom<u64> for u32`. Docs example:
//!
//! ```rust
//! let big_number = 1_000_000_000_000i64;
//! let invalid: Result<u32, _> = u32::try_from(big_number);
//! assert!(invalid.is_err());
//!
//! let max_value = u32::MAX as i64;
//! let valid = u32::try_from(max_value);
//! assert_eq!(valid, Ok(u32::MAX));
//! ```
//!
//! We adapt from `i64` to `u64` since the original list item is specifically
//! `TryFrom<u64>` (not i64).

fn make_big() -> u64 {
    1_000_000_000_000_u64
}
fn make_small() -> u64 {
    42_u64
}

#[verify::test]
pub fn test_u32_try_from_u64_overflow() {
    let big = make_big();
    let r: Result<u32, _> = u32::try_from(big);
    assert!(r.is_err());
}

#[verify::test]
pub fn test_u32_try_from_u64_fits() {
    let small = make_small();
    let r: Result<u32, _> = u32::try_from(small);
    match r {
        Ok(v) => assert!(v == 42),
        Err(_) => panic!(),
    }
}

#[verify::test]
pub fn test_u32_try_from_u64_max() {
    let v: u64 = u32::MAX as u64;
    let r: Result<u32, _> = u32::try_from(v);
    match r {
        Ok(x) => assert!(x == u32::MAX),
        Err(_) => panic!(),
    }
}
