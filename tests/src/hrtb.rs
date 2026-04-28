//@ [!lean] skip
//! Regression tests for higher-rank trait bounds in trait clauses.
//!
//! - `f`: https://github.com/AeneasVerif/aeneas/issues/891 (Charon-introduced
//!   HRTB from `Fn(&_)` desugaring)
//! - `test`: https://github.com/AeneasVerif/aeneas/issues/801 (user-written
//!   `for<'a>` HRTB on a custom trait)
//! - `g`: HRTB with `FnMut` and a non-unit output, exercising the same
//!   code path with a different trait family.

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
