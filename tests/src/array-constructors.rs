//@ [!lean] skip
//@ [lean] subdir=ArrayConstructors
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of array constructors (`core::array::from_fn`).
//!
//! `identity`, `double`, `evens` and `powers_of_two` are the examples of the documentation of
//! `core::array::from_fn` (<https://doc.rust-lang.org/std/array/fn.from_fn.html>).

pub fn identity() -> [usize; 5] {
    core::array::from_fn(|i| i)
}

#[verify::test]
pub fn test_identity() {
    assert_eq!(identity(), [0, 1, 2, 3, 4]);
}

pub fn double() -> [usize; 8] {
    core::array::from_fn(|i| i * 2)
}

#[verify::test]
pub fn test_double() {
    assert_eq!(double(), [0, 2, 4, 6, 8, 10, 12, 14]);
}

pub fn evens() -> [bool; 5] {
    core::array::from_fn(|i| i % 2 == 0)
}

#[verify::test]
pub fn test_evens() {
    assert_eq!(evens(), [true, false, true, false, true]);
}

pub fn powers_of_two() -> [i32; 6] {
    let mut state = 1;
    core::array::from_fn(move |_| {
        let x = state;
        state *= 2;
        x
    })
}

#[verify::test]
pub fn test_powers_of_two() {
    assert_eq!(powers_of_two(), [1, 2, 4, 8, 16, 32]);
}

/// Closure which owns and updates a counter, and also uses the index.
pub fn counter() -> [u32; 4] {
    let mut counter = 0u32;
    core::array::from_fn(move |i| {
        counter += 1;
        counter * 100 + i as u32
    })
}

#[verify::test]
pub fn test_counter() {
    assert_eq!(counter(), [100, 201, 302, 403]);
}

/// `N = 0`: the closure is never called.
#[verify::test]
pub fn test_empty() {
    let a: [u32; 0] = core::array::from_fn(|_| panic!());
    assert_eq!(a.len(), 0);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_fn() {
        test_identity();
        test_double();
        test_evens();
        test_powers_of_two();
        test_counter();
        test_empty();
    }
}
