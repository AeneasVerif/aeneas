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

/// Rust docs example:
/// <https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.enumerate>
///
/// ```ignore
/// let a = ['a', 'b', 'c'];
/// let mut iter = a.iter().enumerate();
/// iter.next() == Some((0, &'a'));
/// iter.next() == Some((1, &'b'));
/// iter.next() == Some((2, &'c'));
/// iter.next() == None;
/// ```
#[verify::test]
pub fn test_enumerate_docs_example() {
    let a: [char; 3] = ['a', 'b', 'c'];
    let mut iter = a.iter().enumerate();
    let (i0, x0) = iter.next().unwrap();
    assert!(i0 == 0 && *x0 == 'a');
    let (i1, x1) = iter.next().unwrap();
    assert!(i1 == 1 && *x1 == 'b');
    let (i2, x2) = iter.next().unwrap();
    assert!(i2 == 2 && *x2 == 'c');
    assert!(iter.next().is_none());
}
