//@ [!lean] skip
//! Regression test for https://github.com/AeneasVerif/aeneas/issues/1051 (When a trait has two
//! parent clauses that derive the same field name, name collision would happen.
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

// Example 4: Two parent clauses of the same generic trait, they differ in a type argument. These
// don't need deduplication since the base names shouldn't collide.
pub trait Gen<T> {
    fn get(&self) -> T;
}

pub trait UsesGen: Gen<u8> + Gen<u16> {}

// Example 5: Two parent clauses of the same generic trait, they differ in a const-generic argument.
// These don't need deduplication since the base names shouldn't collide.
pub trait GenN<const N: usize> {}

pub trait UsesGenN: GenN<3> + GenN<5> {}

// Example 6: The specific combination of names causes a collision. I.e.,
// `Parent`+`Self`+`Foo`+`SideBar` = `ParentSelfFooSideBar`
// `Parent`+`Self`+`FooSide`+`Bar` = `ParentSelfFooSideBar`

pub struct Foo;
pub struct SideBar;
pub struct FooSide;
pub struct Bar;

pub trait Parent<T, U> {}

pub trait Combined: Parent<Foo, SideBar> + Parent<FooSide, Bar> {}

