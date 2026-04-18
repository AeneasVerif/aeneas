//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `Step for i32` (the unstable `core::iter::range::Step` trait).
//!
//! `Step` is unstable and not directly callable from user code; it's the
//! iteration machinery behind `for i in a..b { ... }` ranges. These tests
//! exercise it through that surface syntax, which is the observable behaviour
//! documented at <https://doc.rust-lang.org/core/iter/trait.Step.html>.

fn make_start() -> i32 { -2 }
fn make_end() -> i32 { 3 }

#[verify::test]
pub fn test_i32_range_sum() {
    let s: i32 = make_start();
    let e: i32 = make_end();
    let mut total: i32 = 0;
    for i in s..e {
        total = total + i;
    }
    // -2 + -1 + 0 + 1 + 2 = 0
    assert!(total == 0);
}

#[verify::test]
pub fn test_i32_range_count() {
    let s: i32 = make_start();
    let e: i32 = make_end();
    let mut n: i32 = 0;
    for _ in s..e {
        n = n + 1;
    }
    assert!(n == 5);
}
