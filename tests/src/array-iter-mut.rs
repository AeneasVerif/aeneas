//@ [!lean] skip
//@ [lean] subdir=ArrayIterMut
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean model of `IntoIterator for &mut [T; N]`.
//!
//! `add_two` adapts the example of the documentation
//! (<https://doc.rust-lang.org/std/primitive.slice.html#method.iter_mut>).

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
