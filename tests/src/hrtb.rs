//@ [!lean] skip
//! Regression tests for higher-rank trait bounds.
//!
//! - `f`: https://github.com/AeneasVerif/aeneas/issues/891 (Charon-introduced
//!   HRTB from `Fn(&_)` desugaring)
//! - `test`: https://github.com/AeneasVerif/aeneas/issues/801 (user-written
//!   `for<'a>` HRTB on a custom trait)
//! - `g`: HRTB with `FnMut` and a non-unit output, exercising the same
//!   code path with a different trait family.
//! - `callee` / `caller`: minimal HRTB-bounded caller→callee chain. This
//!   is exactly what fails when a function call passes a HRTB-bounded
//!   generic type parameter forward to another function.
//! - `cond_negate` / `trigger`: in-tree analog of the small reproducer
//!   from https://github.com/AeneasVerif/aeneas/issues/765 (the
//!   `subtle::ConditionallyNegatable` example), using a blanket impl
//!   whose where-clause is `for<'a> &'a Self: Neg<Output = Self>`. The
//!   `subtle`-using version requires an external crate; this in-tree
//!   version reaches the same `instantiate_fun_sig` crash site.

fn f<P: Fn(&usize)>(p: P) {
    p(&1)
}

trait T<X> {
    fn dummy() -> X;
}

fn test<P: for<'a> T<&'a u8>>() -> u8 {
    *P::dummy()
}

fn g<P: FnMut(&usize) -> u8>(mut p: P) -> u8 {
    let _ = p(&0);
    p(&1)
}

trait Tr<'a> {}

fn callee<P: for<'a> Tr<'a>>() {}

fn caller<P: for<'a> Tr<'a>>() {
    callee::<P>()
}

#[derive(Clone, Copy)]
pub struct UnitField;

pub trait Neg {
    type Output;
    fn neg(self) -> Self::Output;
}

impl<'a> Neg for &'a UnitField {
    type Output = UnitField;
    fn neg(self) -> UnitField {
        UnitField
    }
}

pub trait CondNegate {
    fn cond_negate(&mut self);
}

impl<T: Copy> CondNegate for T
where
    for<'a> &'a T: Neg<Output = T>,
{
    fn cond_negate(&mut self) {
        let n = (&*self).neg();
        *self = n;
    }
}

pub fn trigger() {
    let mut x = UnitField;
    x.cond_negate();
}
