//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Test for `core::array::from_fn`. Verbatim from
//! <https://doc.rust-lang.org/core/array/fn.from_fn.html>:
//!
//! ```
//! let array = core::array::from_fn(|i| i);
//! assert_eq!(array, [0, 1, 2, 3, 4]);
//! ```

#[verify::test]
pub fn test_from_fn_identity() {
    let array: [usize; 5] = core::array::from_fn(|i| i);
    assert!(array[0] == 0);
    assert!(array[1] == 1);
    assert!(array[2] == 2);
    assert!(array[3] == 3);
    assert!(array[4] == 4);
}
