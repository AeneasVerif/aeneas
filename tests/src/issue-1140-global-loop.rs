//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/1140
//! Loops within `const`/`static` items used to trigger an internal error.
//!
//! Note: anonymous `const _` items are not exercised here because they
//! independently translate to an invalid Lean identifier (`def _`),
//! regardless of whether they contain a loop.

// A loop in a `static` item.
pub static S: u32 = {
    let mut i = 0;
    while i < 3 {
        i += 1;
    }
    i
};

// A loop in a named `const` item.
pub const C: u32 = {
    let mut sum = 0;
    let mut i = 0;
    while i < 5 {
        sum += i;
        i += 1;
    }
    sum
};
