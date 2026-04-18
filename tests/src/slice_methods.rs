//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `[T]::clone_from_slice`, `[T]::copy_within`, and the
//! cross-type `PartialEq<[U; N]> for [T]` impl. Adapted from the Rust
//! docs examples for each method.

fn make_src() -> [u32; 4] {
    [10, 20, 30, 40]
}

#[verify::test]
pub fn test_clone_from_slice() {
    // Adapted from <https://doc.rust-lang.org/core/primitive.slice.html#method.clone_from_slice>
    let src: [u32; 4] = make_src();
    let mut dst: [u32; 4] = [0, 0, 0, 0];
    dst.clone_from_slice(&src);
    assert!(dst[0] == 10);
    assert!(dst[3] == 40);
}

#[verify::test]
pub fn test_copy_within_basic() {
    // Adapted from <https://doc.rust-lang.org/core/primitive.slice.html#method.copy_within>
    // let mut bytes = *b"Hello, World!";
    // bytes.copy_within(1..5, 8);
    let mut a: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a.copy_within(1..5, 0);
    assert!(a[0] == 2);
    assert!(a[3] == 5);
    assert!(a[4] == 5);
}

#[verify::test]
pub fn test_partial_eq_slice_array() {
    // PartialEq<[U; N]> for [T]: a slice equals an array when lengths match
    // and all elements compare equal pairwise.
    let v: [u32; 3] = [1, 2, 3];
    let s: &[u32] = &v[..];
    assert!(s == &[1u32, 2, 3]);
}
