//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of division operations on unsigned integers (`div_ceil`), verifying the model matches Rust behavior.

/// The example from the documentation of `div_ceil`
/// (<https://doc.rust-lang.org/std/primitive.usize.html#method.div_ceil>), which is the same for
/// every unsigned type.
#[verify::test]
pub fn test_div_ceil_doc() {
    assert_eq!(7_u8.div_ceil(4), 2);
    assert_eq!(7_u16.div_ceil(4), 2);
    assert_eq!(7_u32.div_ceil(4), 2);
    assert_eq!(7_u64.div_ceil(4), 2);
    assert_eq!(7_u128.div_ceil(4), 2);
    assert_eq!(7_usize.div_ceil(4), 2);
}

/// Edge cases: no overflow near `MAX`.
#[verify::test]
pub fn test_div_ceil_edges() {
    assert_eq!(0_u8.div_ceil(7), 0);
    assert_eq!(9_u8.div_ceil(3), 3);
    assert_eq!(255_u8.div_ceil(1), 255);
    assert_eq!(255_u8.div_ceil(2), 128);
    assert_eq!(255_u8.div_ceil(255), 1);
    assert_eq!(254_u8.div_ceil(255), 1);
    assert_eq!(usize::MAX.div_ceil(1), usize::MAX);
    // Not inlined in `assert_eq!`: rustc would promote it to a constant using an unchecked
    // division, which Aeneas extracts to the missing `Usize.div`.
    let half = usize::MAX / 2 + 1;
    assert_eq!(usize::MAX.div_ceil(2), half);
    assert_eq!(usize::MAX.div_ceil(usize::MAX), 1);
    assert_eq!((usize::MAX - 1).div_ceil(usize::MAX), 1);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn div_ceil_doc() {
        test_div_ceil_doc();
    }

    #[test]
    fn div_ceil_edges() {
        test_div_ceil_edges();
    }
}
