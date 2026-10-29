//@ [!lean] skip
//@ [lean] subdir=ArrayIterMut
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean model of `IntoIterator for &mut [T; N]`.
//!
//! `add_two` adapts the example of the documentation of `slice::iter_mut`
//! (<https://doc.rust-lang.org/std/primitive.slice.html#method.iter_mut>), which
//! `IntoIterator for &mut [T; N]` calls.

/// The doc example iterates over `x.iter_mut()`: to exercise this model, the loop iterates over
/// `x` (an `&mut [i32; N]`) directly.
pub fn add_two<const N: usize>(x: &mut [i32; N]) {
    for elem in x {
        *elem += 2;
    }
}

#[verify::test]
pub fn test_add_two() {
    let mut x = [1, 2, 4];
    add_two(&mut x);
    assert_eq!(x, [3, 4, 6]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array_iter_mut() {
        test_add_two();
    }
}
