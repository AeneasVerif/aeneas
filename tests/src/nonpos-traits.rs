//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Traits that break positivity: a method takes another implementor of the same trait.
//! In Lean, such a trait can't be an ordinary `structure`, so Aeneas emits a `nonpos_structure`.
//!
//! The `#[verify::test]` functions are run by Lean (`#guard`), with the compiled code of the
//! dictionaries, including impls which refer to themselves; `cargo test` runs them in Rust.
//! The shapes that `nonpos-iterator.rs` (a copy of the std iterator traits) has are not repeated
//! here: mutual groups, supertraits inside a group, associated types, const generics, loops.

/// - a supertrait from outside the group (`Clone`), and a bound on an associated type (`Item`):
///   plain fields holding the other trait's dictionary.  (Not `Item: Clone`: Aeneas would name
///   both fields `corecloneCloneInst`.)
/// - an associated constant: a plain field holding a value of the monad;
/// - provided methods: an impl which uses them refers to itself (`partial_fixpoint`).  `double`
///   has no generics, so the impl's field is `ExampleNonpos.double.default X`, which mentions `X` itself; it
///   runs because the fields of a dictionary are only evaluated when it is first used
///   (`Fix.foldDelayed`).
pub trait ExampleNonpos: Clone {
    type Item: Default;
    const BASE: u32;
    fn to_num(&self) -> u32;
    fn item(&self) -> Self::Item;
    fn add<Other: ExampleNonpos>(&self, other: &Other) -> u32;
    fn bigger<Other: ExampleNonpos>(&self, other: &Other) -> bool {
        self.to_num() > other.to_num()
    }
    fn double(&self) -> u32 {
        self.to_num() + self.to_num()
    }
}

impl ExampleNonpos for u32 {
    type Item = u32;
    const BASE: u32 = 10;
    fn to_num(&self) -> u32 {
        *self
    }
    fn item(&self) -> u32 {
        *self
    }
    fn add<Other: ExampleNonpos>(&self, other: &Other) -> u32 {
        *self + other.to_num()
    }
}

/// A generic impl, which also refers to itself (through the provided methods).
#[derive(Clone)]
pub struct Wrapper<T> {
    pub x: T,
}

impl<T: ExampleNonpos> ExampleNonpos for Wrapper<T> {
    type Item = T::Item;
    const BASE: u32 = T::BASE + 1;
    fn to_num(&self) -> u32 {
        self.x.to_num()
    }
    fn item(&self) -> T::Item {
        self.x.item()
    }
    fn add<Other: ExampleNonpos>(&self, other: &Other) -> u32 {
        self.x.add(other)
    }
}

/// Through the dictionary: its projections, and its supertrait and associated constant.
pub fn double_of<B: ExampleNonpos>(b: &B) -> u32 {
    b.double()
}

pub fn bigger_of<B: ExampleNonpos, C: ExampleNonpos>(b: &B, c: &C) -> bool {
    b.bigger(c)
}

pub fn base_of<B: ExampleNonpos>(_b: &B) -> u32 {
    B::BASE
}

pub fn item_of<B: ExampleNonpos>(b: &B) -> B::Item {
    b.clone().item()
}

pub fn default_item<B: ExampleNonpos>(_b: &B) -> B::Item {
    B::Item::default()
}

/// Mutual recursion taking a dictionary.
pub fn even<B: ExampleNonpos>(b: &B, n: u32) -> u32 {
    if n == 0 { b.to_num() } else { odd(b, n - 1) }
}

pub fn odd<B: ExampleNonpos>(b: &B, n: u32) -> u32 {
    if n == 0 { 1 } else { even(b, n - 1) }
}

#[verify::test]
pub fn test_methods() {
    assert!(3u32.add(&4u32) == 7);
    assert!(Wrapper { x: 3u32 }.add(&4u32) == 7);
    assert!(3u32.add(&Wrapper { x: 4u32 }) == 7);
}

#[verify::test]
pub fn test_self_referential() {
    assert!(3u32.double() == 6);
    assert!(double_of(&3u32) == 6);
    assert!(!bigger_of(&3u32, &4u32));
    assert!(bigger_of(&Wrapper { x: 4u32 }, &3u32));
    assert!(double_of(&Wrapper { x: 5u32 }) == 10);
}

#[verify::test]
pub fn test_plain_fields() {
    assert!(base_of(&3u32) == 10);
    assert!(base_of(&Wrapper { x: 3u32 }) == 11);
    assert!(item_of(&7u32) == 7);
    assert!(item_of(&Wrapper { x: 7u32 }) == 7);
    assert!(default_item(&Wrapper { x: 7u32 }) == 0);
}

#[verify::test]
pub fn test_recursion() {
    assert!(even(&5u32, 3) == 1);
    assert!(even(&5u32, 2) == 5);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all() {
        test_methods();
        test_self_referential();
        test_plain_fields();
        test_recursion();
    }
}
