//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of array constructors (`core::array::from_fn`), verifying the model matches Rust behavior.
//!
//! The `test_from_fn_doc_*` tests are the examples from the documentation of `core::array::from_fn`
//! (<https://doc.rust-lang.org/std/array/fn.from_fn.html>), except the one building an array of
//! `String`s with `format!` (`format!` and `String == &str` have no Lean models), and with the
//! adaptation explained on `test_from_fn_doc_state`.

#[verify::test]
pub fn test_from_fn_doc_identity() {
    let array = core::array::from_fn(|i| i);
    // indexes are:    0  1  2  3  4
    assert_eq!(array, [0, 1, 2, 3, 4]);
}

#[verify::test]
pub fn test_from_fn_doc_double() {
    let array2: [usize; 8] = core::array::from_fn(|i| i * 2);
    // indexes are:     0  1  2  3  4  5   6   7
    assert_eq!(array2, [0, 2, 4, 6, 8, 10, 12, 14]);
}

#[verify::test]
pub fn test_from_fn_doc_bool() {
    let bool_arr = core::array::from_fn::<_, 5, _>(|i| i % 2 == 0);
    // indexes are:       0     1      2     3      4
    assert_eq!(bool_arr, [true, false, true, false, true]);
}

/// The doc example uses a closure which mutably borrows `state`. Aeneas doesn't support passing such
/// closures yet (see `call_fn_mut` in `closures.rs`), so the closure takes ownership of `state`
/// (`move`) instead. The array is the same since `state` isn't read afterwards.
#[verify::test]
pub fn test_from_fn_doc_state() {
    let mut state = 1;
    let a = std::array::from_fn(move |_| { let x = state; state *= 2; x });
    assert_eq!(a, [1, 2, 4, 8, 16, 32]);
}

/// Closure which owns and updates a counter, and also uses the index: checks that the closure is
/// called in increasing order of the index, and that its state is threaded from one call to the
/// next.
pub fn from_fn_stateful() -> [u32; 4] {
    let mut counter = 0u32;
    core::array::from_fn(move |i| {
        counter += 1;
        counter * 100 + i as u32
    })
}

#[verify::test]
pub fn test_from_fn_stateful() {
    assert_eq!(from_fn_stateful(), [100, 201, 302, 403]);
}

/// `N = 0`: the closure is never called.
#[verify::test]
pub fn test_from_fn_empty() {
    let a: [u32; 0] = core::array::from_fn(|_| panic!());
    assert_eq!(a.len(), 0);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_fn_doc() {
        test_from_fn_doc_identity();
        test_from_fn_doc_double();
        test_from_fn_doc_bool();
        test_from_fn_doc_state();
    }

    #[test]
    fn from_fn() {
        test_from_fn_stateful();
        test_from_fn_empty();
    }
}
