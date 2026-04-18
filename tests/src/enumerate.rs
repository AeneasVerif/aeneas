//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `Iterator::enumerate`, verifying the Aeneas model matches Rust
//! behavior.

/// `enumerate` yields `(index, item)` pairs starting at 0.
#[verify::test]
pub fn test_enumerate_basic() {
    let v: [u32; 3] = [10, 20, 30];
    let mut it = v.iter().enumerate();
    let (i0, x0) = it.next().unwrap();
    assert!(i0 == 0 && *x0 == 10);
    let (i1, x1) = it.next().unwrap();
    assert!(i1 == 1 && *x1 == 20);
    let (i2, x2) = it.next().unwrap();
    assert!(i2 == 2 && *x2 == 30);
    assert!(it.next().is_none());
}

/// `enumerate` on an empty slice yields nothing.
#[verify::test]
pub fn test_enumerate_empty() {
    let v: [u32; 0] = [];
    let mut it = v.iter().enumerate();
    assert!(it.next().is_none());
}

/// `enumerate` on a single-element slice yields `(0, &x)`.
#[verify::test]
pub fn test_enumerate_single() {
    let v: [u32; 1] = [42];
    let mut it = v.iter().enumerate();
    let (i, x) = it.next().unwrap();
    assert!(i == 0 && *x == 42);
    assert!(it.next().is_none());
}

/// Example adapted from the Rust docs:
/// <https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.enumerate>
///
/// TODO: revert this to the verbatim docs example once Aeneas models the
/// following stdlib items (tracked in `funs-external-stdlib.md`):
///   - `char` (primitive type) + `Char::eq`
///   - `Array::into_iter` + `core::array::iter::IntoIter` + Iterator impl
///   - `Option::PartialEq::eq`
///
/// In the meantime: u32 codepoints for 'a'/'b'/'c' (97/98/99), `.iter()`
/// instead of `.into_iter()`, and `.unwrap()` + field-wise comparison
/// instead of `assert_eq!(it.next(), Some((i, x)))`. The `enumerate`
/// semantics being verified are identical.
#[verify::test]
pub fn test_enumerate_docs_example() {
    let a: [u32; 3] = [97, 98, 99];
    let mut iter = a.iter().enumerate();
    let (i0, x0) = iter.next().unwrap();
    assert!(i0 == 0 && *x0 == 97);
    let (i1, x1) = iter.next().unwrap();
    assert!(i1 == 1 && *x1 == 98);
    let (i2, x2) = iter.next().unwrap();
    assert!(i2 == 2 && *x2 == 99);
    assert!(iter.next().is_none());
}
