//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Traits that break positivity: a method takes another implementor of the same trait.
//! In Lean, such a trait can't be an ordinary `structure`, so Aeneas emits a `nonpos_structure`.
//!
//! The `#[verify::test]` functions are run by Lean (`#guard`), with the compiled code of the
//! dictionaries, including the impls which refer to themselves; `cargo test` runs them in Rust.

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

// An impl which refers to itself: `bigger` is a provided method, so the impl of `Sized2` for
// `u32` uses its default, which takes the impl itself as an argument (`partial_fixpoint`).
pub trait Sized2 {
    fn area(&self) -> u32;
    fn bigger<Other: Sized2>(&self, other: &Other) -> bool {
        self.area() > other.area()
    }
    // A provided method with no generics: the impl's field is `Sized2.double.default X`, without
    // a lambda, which mentions `X` itself; it runs because the fields of a dictionary are only
    // evaluated when it is first used (`Fix.foldDelayed`).
    fn double(&self) -> u32 {
        self.area() + self.area()
    }
}

impl Sized2 for u32 {
    fn area(&self) -> u32 {
        *self
    }
}

pub fn use_sized2() -> bool {
    3u32.bigger(&4u32)
}

pub fn use_double() -> u32 {
    3u32.double()
}

// Through the dictionary: its projections, on the impl which refers to itself.
pub fn double_of<S: Sized2>(s: &S) -> u32 {
    s.double()
}

pub fn bigger_of<S: Sized2, T: Sized2>(s: &S, t: &T) -> bool {
    s.bigger(t)
}

// A group of mutually recursive traits: neither trait refers to itself, but each one refers to
// the other.
pub trait Left {
    fn val(&self) -> u32;
    fn via_right<R: Right>(&self, r: &R) -> u32;
}

pub trait Right {
    fn via_left<L: Left>(&self, l: &L) -> u32;
}

impl Left for u32 {
    fn val(&self) -> u32 {
        *self
    }
    // Doesn't call `r.via_left(self)`: an impl method which passes the impl itself as a
    // dictionary is printed before the impl, which Lean rejects (a pre-existing Aeneas
    // limitation, independent of positivity).
    fn via_right<R: Right>(&self, r: &R) -> u32 {
        *self
    }
}

impl Right for u32 {
    fn via_left<L: Left>(&self, l: &L) -> u32 {
        l.val()
    }
}

pub fn use_left_right() -> u32 {
    4u32.via_left(&3u32)
}

// A miniature of the std iterator traits: a mutually recursive group with associated types, a
// supertrait inside the group (`MyDoubleEnded: MyIterator`), provided methods with a loop and with
// other dictionaries, impls which refer to themselves, and a generic impl (`Peek`) which refers to
// itself. See `nonpos-iterator.rs` for a larger copy of the std traits.
pub trait MyIntoIterator {
    type Item;
    type IntoIter: MyIterator<Item = Self::Item>;
    fn into_iter(self) -> Self::IntoIter;
}

pub trait MyIterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
    fn zip_count<U: MyIntoIterator>(&mut self, other: U) -> u32 {
        let mut o = other.into_iter();
        let mut n = 0;
        while let (Some(_), Some(_)) = (self.next(), o.next()) {
            n += 1;
        }
        n
    }
    // Doesn't call `next_back`: Aeneas can't translate that yet (the item type of `MyDoubleEnded`
    // is not identified with `Self::Item`).
    fn rev_first(self) -> Option<Self::Item>
    where
        Self: MyDoubleEnded + Sized,
    {
        None
    }
    fn collect<B: MyFromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        B::from_iter(self)
    }
}

pub trait MyDoubleEnded: MyIterator {
    fn next_back(&mut self) -> Option<Self::Item>;
}

pub trait MyFromIterator<A> {
    fn from_iter<T: MyIterator<Item = A>>(iter: T) -> Self;
}

pub struct Count {
    pub n: u32,
}

impl MyIterator for Count {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            Some(self.n)
        }
    }
}

impl MyDoubleEnded for Count {
    fn next_back(&mut self) -> Option<u32> {
        self.next()
    }
}

impl MyIntoIterator for Count {
    type Item = u32;
    type IntoIter = Count;
    fn into_iter(self) -> Count {
        self
    }
}

impl MyFromIterator<u32> for u32 {
    fn from_iter<T: MyIterator<Item = u32>>(mut iter: T) -> u32 {
        let mut acc = 0;
        while let Some(x) = iter.next() {
            acc += x;
        }
        acc
    }
}

pub struct Peek<I: MyIterator> {
    pub inner: I,
    pub buf: Option<Option<I::Item>>,
}

impl<I: MyIterator> MyIterator for Peek<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        self.inner.next()
    }
}

pub fn sum_count() -> u32 {
    Count { n: 4 }.collect()
}

pub fn sum_peek() -> u32 {
    Peek {
        inner: Count { n: 4 },
        buf: None,
    }
    .collect()
}

pub fn zip_counts() -> u32 {
    Count { n: 3 }.zip_count(Count { n: 5 })
}

// A generic impl: the dictionary of `Wrapper<T>` is built from the one of `T`.
pub struct Wrapper<T> {
    pub x: T,
}

impl<T: Bla> Bla for Wrapper<T> {
    fn to_num(&self) -> u32 {
        self.x.to_num()
    }
    fn add<Other: Bla>(&self, other: &Other) -> u32 {
        self.x.add(other)
    }
}

// An associated constant: a plain field of the dictionary, holding a value of the monad.
pub trait WithConst {
    const BASE: u32;
    fn scaled<O: WithConst>(&self, o: &O) -> u32;
}

impl WithConst for u32 {
    const BASE: u32 = 10;
    fn scaled<O: WithConst>(&self, _o: &O) -> u32 {
        *self * O::BASE
    }
}

// A const generic parameter.
pub trait Bounded<const N: usize> {
    fn cap(&self) -> usize;
    fn fits<O: Bounded<N>>(&self, o: &O) -> bool;
}

impl<const N: usize> Bounded<N> for u32 {
    fn cap(&self) -> usize {
        N
    }
    fn fits<O: Bounded<N>>(&self, o: &O) -> bool {
        (*self as usize) <= o.cap()
    }
}

// Bounds on a trait from outside the group (`Clone`): as a supertrait, and on an associated type.
// Aeneas emits each such bound as a plain field of the `nonpos_structure` that holds the other
// trait's dictionary.
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

// Functions taking a dictionary: a loop, and mutual recursion.
pub fn count_down<B: Bla>(b: &B, n: u32) -> u32 {
    let mut n = n;
    let mut acc = 0;
    while n > 0 {
        acc += b.to_num();
        n -= 1;
    }
    acc
}

pub fn even<B: Bla>(b: &B, n: u32) -> u32 {
    if n == 0 { b.to_num() } else { odd(b, n - 1) }
}

pub fn odd<B: Bla>(b: &B, n: u32) -> u32 {
    if n == 0 { 1 } else { even(b, n - 1) }
}

// Tests, run in Lean with the compiled code.

#[verify::test]
pub fn test_bla() {
    assert!(use_bla() == 7);
    assert!(Wrapper { x: 3u32 }.add(&4u32) == 7);
    assert!(3u32.add(&Wrapper { x: 4u32 }) == 7);
}

#[verify::test]
pub fn test_sized2() {
    assert!(!use_sized2());
    assert!(4u32.bigger(&3u32));
}

#[verify::test]
pub fn test_double() {
    assert!(use_double() == 6);
    assert!(double_of(&3u32) == 6);
    assert!(bigger_of(&4u32, &3u32));
}

#[verify::test]
pub fn test_left_right() {
    assert!(use_left_right() == 3);
}

#[verify::test]
pub fn test_iterators() {
    assert!(sum_count() == 6);
    assert!(sum_peek() == 6);
    assert!(zip_counts() == 3);
}

#[verify::test]
pub fn test_const_and_params() {
    assert!(2u32.scaled(&3u32) == 20);
    assert!(Bounded::<5>::fits(&3u32, &4u32));
    assert!(!Bounded::<2>::fits(&3u32, &4u32));
}

#[verify::test]
pub fn test_foreign_bounds() {
    assert!(use_foo(&5u32) == 5);
    assert!(2u32.combine(&3u32) == 5);
    assert!(use_bar(&7u32) == 7);
}

#[verify::test]
pub fn test_dictionary_arguments() {
    assert!(count_down(&3u32, 4) == 12);
    assert!(even(&5u32, 3) == 1);
    assert!(even(&5u32, 2) == 5);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all() {
        test_bla();
        test_sized2();
        test_double();
        test_left_right();
        test_iterators();
        test_const_and_params();
        test_foreign_bounds();
        test_dictionary_arguments();
    }
}
