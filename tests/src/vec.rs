//@ [coq,fstar,borrow-check] skip
#![feature(register_tool)]
#![register_tool(verify)]

use std::vec::Vec;

fn use_extend_from_slice<T: Clone>(v: &mut Vec<T>, s: &[T]) {
    v.extend_from_slice(s)
}

fn use_alloc_with_capacity<T>(n: usize) -> Vec<T> {
    Vec::with_capacity(n)
}

fn from_elem<T: Clone>(x: T, n: usize) -> Vec<T> {
    std::vec::from_elem(x, n)
}

#[verify::test]
pub fn test_insert_empty() {
    let mut v = Vec::new();
    v.insert(0, 42u32);
    assert!(v.len() == 1);
    assert!(v[0] == 42);
}

#[verify::test]
pub fn test_insert_at_len() {
    let mut v = Vec::new();
    v.push(10u32);
    v.push(20u32);
    v.insert(v.len(), 30);
    assert!(v.len() == 3);
    assert!(v[0] == 10);
    assert!(v[1] == 20);
    assert!(v[2] == 30);
}

#[verify::test]
pub fn test_insert_middle() {
    let mut v = Vec::new();
    v.push(10u32);
    v.push(20u32);
    v.insert(1, 99);
    assert!(v.len() == 3);
    assert!(v[0] == 10);
    assert!(v[1] == 99);
    assert!(v[2] == 20);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_empty() {
        test_insert_empty();
    }

    #[test]
    fn insert_at_len() {
        test_insert_at_len();
    }

    #[test]
    fn insert_middle() {
        test_insert_middle();
    }

    #[test]
    #[should_panic]
    fn insert_out_of_bounds_empty() {
        let mut v = Vec::new();
        v.insert(1, 42u32);
    }

    #[test]
    #[should_panic]
    fn insert_out_of_bounds_nonempty() {
        let mut v = Vec::new();
        v.push(10u32);
        v.push(20u32);
        v.insert(3, 30);
    }
}
