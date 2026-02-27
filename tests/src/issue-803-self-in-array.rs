//@ [!lean] skip
//! Issue 803: arrays containing `Self` caused an internal error in projections.
//! https://github.com/AeneasVerif/aeneas/issues/803

pub struct Arguments<'a>(&'a ());

impl<'a> Arguments<'a> {
    fn none(x: Self) -> [Self; 1] {
        [x]
    }
}
