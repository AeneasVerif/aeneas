//@ [!lean] skip
//! Traits that break positivity, with bounds on a trait from outside the group (`Clone`): as a
//! supertrait, and on an associated type.  Aeneas emits each such bound as a plain field of the
//! `nonpos_structure` that holds the other trait's dictionary.

/// A supertrait from outside the group.
pub trait Foo: Clone {
    fn get(&self) -> u32;
    fn combine<O: Foo>(&self, other: &O) -> u32;
}

impl Foo for u32 {
    fn get(&self) -> u32 {
        *self
    }
    fn combine<O: Foo>(&self, other: &O) -> u32 {
        *self + other.get()
    }
}

pub fn use_foo<T: Foo>(x: &T) -> u32 {
    x.clone().get()
}

/// A bound on an associated type, from outside the group.
pub trait Bar {
    type Item: Clone;
    fn item(&self) -> Self::Item;
    fn with<O: Bar>(&self, other: &O) -> u32;
}

impl Bar for u32 {
    type Item = u32;
    fn item(&self) -> u32 {
        *self
    }
    fn with<O: Bar>(&self, _other: &O) -> u32 {
        *self
    }
}

pub fn use_bar<T: Bar>(x: &T) -> T::Item {
    x.item().clone()
}
