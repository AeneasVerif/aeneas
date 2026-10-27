//@ [!lean] skip
//! Traits that break positivity: a method takes another implementor of the same trait.
//! In Lean, such a trait can't be an ordinary `structure`, so Aeneas emits a `nonpos_structure`.

pub trait Bla {
    fn to_num(&self) -> u32;
    fn add<Other: Bla>(&self, other: &Other) -> u32;
}

impl Bla for u32 {
    fn to_num(&self) -> u32 {
        *self
    }
    fn add<Other: Bla>(&self, other: &Other) -> u32 {
        *self + other.to_num()
    }
}

pub fn use_bla() -> u32 {
    3u32.add(&4u32)
}
