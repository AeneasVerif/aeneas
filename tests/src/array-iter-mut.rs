//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean model of `IntoIterator for &mut [T; N]`, verifying the model matches Rust behavior.

/// The example from the documentation of `slice::iter_mut`
/// (<https://doc.rust-lang.org/std/primitive.slice.html#method.iter_mut>), which
/// `IntoIterator for &mut [T; N]` calls. Two changes so that it exercises this model: the loop
/// iterates over `&mut *x` (an `&mut [i32; 3]`) instead of `x.iter_mut()`, and the assertion
/// compares `*x` with an array, as `PartialEq<&B> for &mut A` has no Lean model.
#[verify::test]
pub fn test_into_iter_mut() {
    let x = &mut [1, 2, 4];
    for elem in &mut *x {
        *elem += 2;
    }
    assert_eq!(*x, [3, 4, 6]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn into_iter_mut() {
        test_into_iter_mut();
    }
}
