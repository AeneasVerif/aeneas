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

// An impl which refers to itself: `bigger` is a provided method, so the impl of `Sized2` for
// `u32` uses its default, which takes the impl itself as an argument.
// TODO: not supported yet; Aeneas prints the impl with `impl_def`, which doesn't work for a
// `nonpos_structure` (it should use `partial_fixpoint`).
pub trait Sized2 {
    fn area(&self) -> u32;
    fn bigger<Other: Sized2>(&self, other: &Other) -> bool {
        self.area() > other.area()
    }
    // A provided method with no generics: the impl's field is `Sized2.double.default X`, without
    // a lambda, so evaluating `X` evaluates `X` again. TODO: the field must be eta-expanded
    // (`fun x => Sized2.double.default X x`), otherwise the code type-checks but loops when run.
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
// TODO: not supported yet (mutually recursive group, impls which refer to themselves).
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
