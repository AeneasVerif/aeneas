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

/// The same trigger with a free function taking `&S<'a>` instead of `&self`.
pub fn shared_ref_struct_try(s: &S<'_>, x: u8) -> Result<u8, ()> {
    let _ = s.r;
    let y = f(x)?;
    Ok(y)
}

// ============================================================
// Controls: these already translated before the fix.
// ============================================================

pub struct Owned {
    pub r: u8,
}

impl Owned {
    /// The struct owns its data (no reference below `&self`).
    pub fn owned_try(&self, x: u8) -> Result<u8, ()> {
        let y = f(x)?;
        Ok(y)
    }
}

impl<'a> S<'a> {
    /// The call is tail-returned (no intermediate bind).
    pub fn tailcall(&self, x: u8) -> Result<u8, ()> {
        f(x)
    }

    /// `self` is taken by value.
    pub fn byval(self, x: u8) -> Result<u8, ()> {
        let y = f(x)?;
        Ok(y)
    }
}
