//@ [!lean] skip

//! # Regression for Aeneas bug 1533
//! When two branches of a join produce shared borrows of the same loan:
//! - In the `then` branch, `(s1, s2)` holds `(ry, ry)` where `ry = &y` has loan id `bid_y`
//!   and borrow id `bid_ry`.
//! - In the `else` branch, `freeze(&mut z)` introduces a region abstraction `abs_freeze`
//!   holding `{ MB@z, SL@rz }`. `(rz, rz)` holds two copies of `SB@rz`.
//! - When joining the two branches:
//!   - `s1` joins `SB@ry` (left) and `SB@rz` (right), creating `abs_s1 { |SB@ry|, ︙SB@rz︙, SL@s1 }`.
//!   - `s2` joins `SB@ry` (left) and `SB@rz` (right), creating `abs_s2 { |SB@ry|, ︙SB@rz︙, SL@s2 }`.
//!   - `abs_freeze` is projected to the right: `abs_freeze { ︙MB@z︙, ︙SL@rz︙ }`.
//! - During `collapse_ctx`, `abs_s1` and `abs_s2` both merge into `abs_freeze` along `︙SL@rz︙` / `︙SB@rz︙`.
//! - In Aeneas, `merge_abstractions_merge_loan_borrow_pairs` did not deduplicate
//!   `ASharedBorrow (pm, bid, _)` when both merged abstractions held `ASharedBorrow` of the same loan
//!   with the same marker (`pm = pm' = PLeft`).
//! - As a result, the merged abstraction contained duplicate entries `|SB@ry|` and `|SB@ry|`.
//! - In `merge_abstractions_merge_markers`, `try_merge_aborrow_contents` asserts
//!   `[%sanity_check] span (complementary_markers pm0 pm1)`. Because both markers were `PLeft`,
//!   this triggered an assert.

fn freeze<'a>(x: &'a mut i32) -> &'a i32 {
    &*x
}

pub fn duplicate_shared_borrow(cond: bool) -> i32 {
    let mut z = 0;
    let y = 0;
    let ry = &y;
    let (s1, s2) = if cond {
        (ry, ry)
    } else {
        let rz = freeze(&mut z);
        (rz, rz)
    };
    *s1 + *s2 + z
}
