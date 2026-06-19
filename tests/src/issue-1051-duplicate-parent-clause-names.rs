//@ [!lean] skip
//! Regression test for https://github.com/AeneasVerif/aeneas/issues/1051
//! When a trait has two parent clauses that derive the same field name, e.g., two associated types 
//! bounded by the same trait, name collision would happen.
use std::num::NonZeroU8;

// Example 1: `TraitB` has two associated types, both bounded by `TraitA`, so it gets two `TraitA` 
// parent clauses that would collide on the same field name without deduplication.
pub trait TraitA {}

pub trait TraitB {
    type X: TraitA;
    type Y: TraitA;
}

// Example 2: `TraitE`'s two associated types are bounded by different traits, so its parent clauses 
// get distinct base names and need no deduplication: they keep the short form.
pub trait TraitC {}

pub trait TraitE {
    type X: TraitA;
    type Y: TraitC;
}

// Example 3: This function pulls in `NonZeroU8` and hence `ZeroablePrimitive`. This has two `Copy` 
// parent clauses which would collide on the same field name without deduplication.
pub fn get_inner(x: NonZeroU8) -> u8 {
    x.get()
}