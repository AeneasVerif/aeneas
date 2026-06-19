//@ [!lean] skip
use std::num::NonZeroU8;

// This function pulls `NonZeroU8` (and hence `ZeroablePrimitive`) into the translation.
// `ZeroablePrimitive` has two `Copy` parent clauses (`Copy<Self>`, `Copy<Self::NonZeroInner>`),
// which would collide on the same field name without deduplication.
pub fn get_inner(x: NonZeroU8) -> u8 {
    x.get()
}

// `TraitB` has two associated types, both bounded by `TraitA`, so it gets two `TraitA`
// parent clauses that would collide on the same field name without deduplication.
pub trait TraitA {}

pub trait TraitB {
    type X: TraitA;
    type Y: TraitA;
}
