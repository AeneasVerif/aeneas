//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Regression test: in Rust, `MIN % -1` panics on signed integers ("attempt
//! to calculate the remainder with overflow"), and `MIN.checked_rem(-1)` is
//! `None`. The Lean model of the signed remainder only failed on a division by
//! zero, so the translation of `rem_i32(i32::MIN, -1)` returned `ok 0`, and
//! the one of `checked_rem_i32(i32::MIN, -1)` returned `some 0`.

pub fn rem_i32(x: i32, y: i32) -> i32 {
    x % y
}

pub fn rem_i8(x: i8, y: i8) -> i8 {
    x % y
}

pub fn checked_rem_i32(x: i32, y: i32) -> Option<i32> {
    x.checked_rem(y)
}
