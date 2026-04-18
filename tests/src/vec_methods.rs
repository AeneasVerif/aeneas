//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `Vec` methods, verifying the Aeneas models match Rust behavior.

fn make_empty() -> Vec<u32> {
    Vec::new()
}

/// `Vec::is_empty` — verbatim pattern from docs.
///
/// ```rust
/// let mut v = Vec::new();
/// assert!(v.is_empty());
/// v.push(1);
/// assert!(!v.is_empty());
/// ```
#[verify::test]
pub fn test_vec_is_empty_new() {
    let v: Vec<u32> = make_empty();
    assert!(v.is_empty());
}

#[verify::test]
pub fn test_vec_is_empty_after_push() {
    let mut v: Vec<u32> = make_empty();
    v.push(1);
    assert!(!v.is_empty());
}

/// `Vec::clear` — adapted from docs (docs use println!).
///
/// Docs:
/// ```rust
/// let mut v = vec![1, 2, 3];
/// v.clear();
/// assert!(v.is_empty());
/// ```
#[verify::test]
pub fn test_vec_clear() {
    let mut v: Vec<u32> = Vec::with_capacity(4);
    v.push(1);
    v.push(2);
    v.push(3);
    v.clear();
    assert!(v.is_empty());
}

/// `Vec::truncate` — verbatim pattern from docs. Docs show truncating a
/// length-5 vec to 2 elements and asserting `v == [1, 2]`. We use length-
/// based check instead of PartialEq<Vec> (not modelled).
#[verify::test]
pub fn test_vec_truncate_shortens() {
    let mut v: Vec<u32> = Vec::with_capacity(5);
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    v.push(5);
    v.truncate(2);
    assert!(v.len() == 2);
}

#[verify::test]
pub fn test_vec_truncate_noop_if_longer() {
    let mut v: Vec<u32> = Vec::with_capacity(3);
    v.push(1);
    v.push(2);
    v.push(3);
    v.truncate(8);
    assert!(v.len() == 3);
}

/// `Vec::as_slice` — adapted from docs (docs use `io::Write::write`).
///
/// ```rust
/// let buffer = vec![1, 2, 3, 5, 8];
/// io::sink().write(buffer.as_slice()).unwrap();
/// ```
#[verify::test]
pub fn test_vec_as_slice() {
    let mut v: Vec<u32> = Vec::with_capacity(3);
    v.push(10);
    v.push(20);
    v.push(30);
    let s: &[u32] = v.as_slice();
    assert!(s.len() == 3);
}

/// `Vec::remove` — verbatim from docs (docs use `v == [1, 3]`).
///
/// ```rust
/// let mut v = vec![1, 2, 3];
/// assert_eq!(v.remove(1), 2);
/// assert_eq!(v, [1, 3]);
/// ```
#[verify::test]
pub fn test_vec_remove_middle() {
    let mut v: Vec<u32> = Vec::with_capacity(3);
    v.push(1);
    v.push(2);
    v.push(3);
    let x = v.remove(1);
    assert!(x == 2);
    assert!(v.len() == 2);
}

/// `Vec::append` — verbatim pattern from docs.
///
/// ```rust
/// let mut vec = vec![1, 2, 3];
/// let mut vec2 = vec![4, 5, 6];
/// vec.append(&mut vec2);
/// assert_eq!(vec, [1, 2, 3, 4, 5, 6]);
/// assert_eq!(vec2, []);
/// ```
#[verify::test]
pub fn test_vec_append() {
    let mut v1: Vec<u32> = Vec::with_capacity(3);
    v1.push(1);
    v1.push(2);
    v1.push(3);
    let mut v2: Vec<u32> = Vec::with_capacity(3);
    v2.push(4);
    v2.push(5);
    v2.push(6);
    v1.append(&mut v2);
    assert!(v1.len() == 6);
    assert!(v2.is_empty());
}

/// `Vec::split_off` — verbatim pattern from docs.
///
/// ```rust
/// let mut vec = vec![1, 2, 3];
/// let vec2 = vec.split_off(1);
/// assert_eq!(vec, [1]);
/// assert_eq!(vec2, [2, 3]);
/// ```
#[verify::test]
pub fn test_vec_split_off() {
    let mut v: Vec<u32> = Vec::with_capacity(3);
    v.push(1);
    v.push(2);
    v.push(3);
    let v2: Vec<u32> = v.split_off(1);
    assert!(v.len() == 1);
    assert!(v2.len() == 2);
}

/// `Default for Vec<T>::default` — verbatim from docs.
///
/// ```rust
/// let v: Vec<u32> = Vec::default();
/// assert!(v.is_empty());
/// ```
#[verify::test]
pub fn test_vec_default() {
    let v: Vec<u32> = Vec::default();
    assert!(v.is_empty());
}
