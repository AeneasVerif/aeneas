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

// Example 4: Two parent clauses of the *same* generic trait, instantiated at different *concrete*
// type arguments. These must NOT need deduplication: the concrete arguments are already part of the
// base name (fields `GenSelfU8Inst` and `GenSelfU16Inst`), so the bases never collide and no
// discriminator is added. This guards the assumption that the discriminator is only needed for
// associated-type projections, not for concrete type arguments.
pub trait Gen<T> {
    fn get(&self) -> T;
}

pub trait UsesGen: Gen<u8> + Gen<u16> {}

// Example 5: Same as Example 4, but the differing argument is a const generic. It likewise ends up
// in the base name (fields `GenNSelf3Inst` and `GenNSelf5Inst`) rather than needing a discriminator.
pub trait GenN<const N: usize> {}

pub trait UsesGenN: GenN<3> + GenN<5> {}
