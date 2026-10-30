//@ [!lean] skip
//@ [lean] subdir=VecMethods
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `Vec` methods (`Vec::is_empty`).
//!
//! `new_is_empty` and `pushed_is_empty` are the examples of the documentation of
//! `Vec::is_empty` (<https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty>).

pub fn new_is_empty() -> bool {
    let v: Vec<i32> = Vec::new();
    v.is_empty()
}

#[verify::test]
pub fn test_new_is_empty() {
    assert!(new_is_empty());
}

pub fn pushed_is_empty() -> bool {
    let mut v = Vec::new();
    v.push(1);
    v.is_empty()
}

#[verify::test]
pub fn test_pushed_is_empty() {
    assert!(!pushed_is_empty());
}

/// `is_empty` guarding an index: the first element, or `default` for an empty vector.
pub fn first_or(v: &Vec<u32>, default: u32) -> u32 {
    if v.is_empty() {
        default
    } else {
        v[0]
    }
}

#[verify::test]
pub fn test_first_or() {
    let mut v = Vec::new();
    assert_eq!(first_or(&v, 7), 7);
    v.push(3);
    assert_eq!(first_or(&v, 7), 3);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vec_methods() {
        test_new_is_empty();
        test_pushed_is_empty();
        test_first_or();
    }
}
