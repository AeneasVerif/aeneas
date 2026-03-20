//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for step_by iterator adapter, verifying the model matches Rust behavior.

/// step_by(1) returns all elements
#[verify::test]
pub fn test_step_by_1() {
    let v: [u32; 5] = [0, 1, 2, 3, 4];
    let mut it = v.iter().step_by(1);
    assert!(*it.next().unwrap() == 0);
    assert!(*it.next().unwrap() == 1);
    assert!(*it.next().unwrap() == 2);
    assert!(*it.next().unwrap() == 3);
    assert!(*it.next().unwrap() == 4);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by(2) returns every other element
pub fn test_step_by_2() {
    let v: [u32; 5] = [0, 1, 2, 3, 4];
    let mut it = v.iter().step_by(2);
    assert!(*it.next().unwrap() == 0);
    assert!(*it.next().unwrap() == 2);
    assert!(*it.next().unwrap() == 4);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by(3)
pub fn test_step_by_3() {
    let v: [u32; 7] = [0, 1, 2, 3, 4, 5, 6];
    let mut it = v.iter().step_by(3);
    assert!(*it.next().unwrap() == 0);
    assert!(*it.next().unwrap() == 3);
    assert!(*it.next().unwrap() == 6);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by larger than collection: returns only the first element
pub fn test_step_by_larger_than_len() {
    let v: [u32; 3] = [0, 1, 2];
    let mut it = v.iter().step_by(10);
    assert!(*it.next().unwrap() == 0);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by on empty slice
pub fn test_step_by_empty() {
    let v: [u32; 0] = [];
    let mut it = v.iter().step_by(2);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by(1) on single element
pub fn test_step_by_single() {
    let v: [u32; 1] = [42];
    let mut it = v.iter().step_by(1);
    assert!(*it.next().unwrap() == 42);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by(2) on single element
pub fn test_step_by_single_step_2() {
    let v: [u32; 1] = [42];
    let mut it = v.iter().step_by(2);
    assert!(*it.next().unwrap() == 42);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by equal to length: returns only the first element
pub fn test_step_by_eq_len() {
    let v: [u32; 3] = [0, 1, 2];
    let mut it = v.iter().step_by(3);
    assert!(*it.next().unwrap() == 0);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by = length - 1
pub fn test_step_by_len_minus_1() {
    let v: [u32; 3] = [0, 1, 2];
    let mut it = v.iter().step_by(2);
    assert!(*it.next().unwrap() == 0);
    assert!(*it.next().unwrap() == 2);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by(2) on two elements: returns only the first
pub fn test_step_by_two_elements() {
    let v: [u32; 2] = [0, 1];
    let mut it = v.iter().step_by(2);
    assert!(*it.next().unwrap() == 0);
    assert!(it.next().is_none());
}

#[verify::test]
/// step_by(4) on a longer sequence
pub fn test_step_by_4_on_longer() {
    let v: [u32; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
    let mut it = v.iter().step_by(4);
    assert!(*it.next().unwrap() == 0);
    assert!(*it.next().unwrap() == 4);
    assert!(*it.next().unwrap() == 8);
    assert!(it.next().is_none());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_by_1() { test_step_by_1(); }
    #[test]
    fn step_by_2() { test_step_by_2(); }
    #[test]
    fn step_by_3() { test_step_by_3(); }
    #[test]
    fn step_by_larger_than_len() { test_step_by_larger_than_len(); }
    #[test]
    fn step_by_empty() { test_step_by_empty(); }
    #[test]
    fn step_by_single() { test_step_by_single(); }
    #[test]
    fn step_by_single_step_2() { test_step_by_single_step_2(); }
    #[test]
    fn step_by_eq_len() { test_step_by_eq_len(); }
    #[test]
    fn step_by_len_minus_1() { test_step_by_len_minus_1(); }
    #[test]
    fn step_by_two_elements() { test_step_by_two_elements(); }
    #[test]
    fn step_by_4_on_longer() { test_step_by_4_on_longer(); }

    #[test]
    #[should_panic]
    fn step_by_0_panics() {
        let v: [u32; 3] = [1, 2, 3];
        v.iter().step_by(0);
    }
}
