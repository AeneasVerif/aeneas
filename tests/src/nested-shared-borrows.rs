//@ [!lean] skip
//! Tests for nested borrows appearing *below a shared borrow*.
//!
//! Regression tests for:
//! - https://github.com/AeneasVerif/aeneas/issues/1099
//! - https://github.com/AeneasVerif/aeneas/issues/1170

// ============================================================
// Issue #1099: `&&u8` (shared borrow of a shared borrow) + `?`
// ============================================================

fn do_option() -> Option<()> {
    Some(())
}

/// A shared borrow of a shared borrow (`&&u8`) with an intermediate `?`.
pub fn double_ref_option(_arg: &&u8) -> Option<()> {
    do_option()?;
    Some(())
}

fn do_result() -> Result<(), ()> {
    Ok(())
}

/// Same as above, but with `Result` instead of `Option`.
pub fn double_ref_result(_arg: &&u8) -> Result<(), ()> {
    do_result()?;
    Ok(())
}

// ============================================================
// Issue #1170: `&self` on a struct storing a reference + `?`
// ============================================================

pub struct S<'a> {
    pub r: &'a u8,
}

fn f(x: u8) -> Result<u8, ()> {
    Ok(x)
}

impl<'a> S<'a> {
    /// `&self` borrows a value (`S<'a>`) whose type contains a reference, and
    /// the intermediate call `f(x)?` binds a result used afterwards.
    pub fn method_try(&self, x: u8) -> Result<u8, ()> {
        let y = f(x)?;
        Ok(y)
    }
}

// ============================================================
// Issue #929: `&self` + an array of shared references + a loop
// ============================================================

pub struct H<T>(pub T);

impl<T> H<T> {
    /// The loop-carried `max : Option<&T>` is a shared borrow nested below the
    /// `Option` ADT, and `arr[i]` reborrows `&self.0` (a `& &T`). Verifying the
    /// loop fixed point exercises joining `None` with `Some(&_)` (nested shared
    /// borrow) and the region-abstraction bookkeeping across loop iterations.
    pub fn find_max(&self) -> Option<&T> {
        let mut max: Option<&T> = None;
        let arr = [&self.0];
        for i in 0..1usize {
            max = Some(arr[i]);
        }
        max
    }
}

/// Same loop-carried `Option<&T>` pattern as `H::find_max`, but without the
/// extra nesting introduced by `&self` and the intermediate array: this
/// exercises the loop-fixed-point region reconciliation (joining `None` at
/// loop entry with `Some(&arr[i])` at the loop head) on a plain slice.
pub fn find_max_slice<T>(arr: &[T]) -> Option<&T> {
    let mut max: Option<&T> = None;
    let mut i = 0;
    while i < arr.len() {
        max = Some(&arr[i]);
        i += 1;
    }
    max
}
