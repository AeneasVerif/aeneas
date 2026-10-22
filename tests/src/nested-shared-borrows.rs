//@ [!lean] skip
//! Tests for nested borrows appearing *below a shared borrow*.
//!
//! Regression tests for:
//! - https://github.com/AeneasVerif/aeneas/issues/1099
//! - https://github.com/AeneasVerif/aeneas/issues/1170
//! - https://github.com/AeneasVerif/aeneas/issues/1393
#![feature(register_tool)]
#![register_tool(verify)]

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

#[verify::test]
pub fn shared_reborrow_same_tuple() {
    let y = (0, 0);
    let mut x = ((1, 2), &y);
    x.1 = &x.0;
    let xr = &x;
    let x11r = &(*(*xr).1).1;
    assert!(*x11r == 2);
    assert!(xr.0 .0 == 1);
    assert!(xr.1 .0 == 1);
}

#[verify::test]
pub fn shared_reborrow_same_box() {
    let y = (0, 0);
    let mut x = Box::new(((1, 2), &y));
    x.1 = &x.0;
    let xr = &x;
    let x11r = &(*(*xr).1).1;
    assert!(*x11r == 2);
    assert!(xr.0 .0 == 1);
}

#[verify::test]
pub fn shared_reborrow_inside_mut_borrow() {
    let y = (0, 0);
    let mut x = ((1, 2), &y);
    let xm = &mut x;
    xm.1 = &xm.0;
    let xr = &xm;
    let x11r = &(*(**xr).1).1;
    assert!(*x11r == 2);
    assert!(xr.0 .0 == 1);
    // Break the self-reference before ending the enclosing mutable borrow.
    xm.1 = &y;
}

pub fn shared_reborrow_from_input<'a>(x: &'a ((u32, u32), &'a (u32, u32))) -> &'a u32 {
    &(*x.1).1
}

#[verify::test]
pub fn shared_reborrow_from_input_test() {
    let y = (0, 0);
    let mut x = ((1, 2), &y);
    x.1 = &x.0;
    let r = shared_reborrow_from_input(&x);
    assert!(*r == 2);
}
