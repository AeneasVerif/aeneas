//@ [!lean] skip

//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1051
//!
//! `core::num::nonzero::ZeroablePrimitive` has two super-traits which are both
//! `Copy`, instantiated with different type arguments (`Self` and
//! `Self::NonZeroInner`). Before the fix, Aeneas generated the same field name
//! for both parent clauses, producing a structure with duplicate fields.

pub fn get_inner(x: core::num::NonZeroU8) -> u8 {
    x.get()
}
