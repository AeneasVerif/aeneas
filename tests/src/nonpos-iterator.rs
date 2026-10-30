//@ [!lean] skip
//! A copy of the std iterator traits (`Iterator`, `IntoIterator`, `FromIterator`,
//! `DoubleEndedIterator`, `Sum`), with the signatures of std for the methods below, a few
//! adapters (`Rev`, `Take`, `Map`, `Zip`, ...), and a blanket `IntoIterator` impl.
//!
//! These traits are mutually recursive and break positivity, so Aeneas extracts them as
//! `nonpos_structure`s. Left out for now, because of front-end limitations unrelated to
//! positivity: `copied`, `cloned`, `unzip` (`where Self: Iterator<Item = ...>`), `rposition`
//! (methods calling `next_back` through a `where` clause), and `by_ref` (`impl Iterator for &mut I`).
//! We also avoid `?` on `Option`, which is extracted to an axiom.
//! TODO: not supported yet (mutually recursive groups, impls which refer to themselves).
pub trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;
    fn into_iter(self) -> Self::IntoIter;
}
pub trait FromIterator<A>: Sized {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self;
}
pub trait DoubleEndedIterator: Iterator {
    fn next_back(&mut self) -> Option<Self::Item>;
}
pub trait Sum<A = Self>: Sized {
    fn sum<I: Iterator<Item = A>>(iter: I) -> Self;
}
pub trait Extend<A> {
    fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T);
}
pub trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
    // collect: always present, it is what closes the cycle with FromIterator/IntoIterator
    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        B::from_iter(self)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
    fn count(self) -> usize
    where
        Self: Sized,
    {
        let mut s = self;
        let mut n = 0;
        while let Some(_) = s.next() {
            n += 1;
        }
        n
    }
    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        let mut s = self;
        let mut l = None;
        while let Some(x) = s.next() {
            l = Some(x);
        }
        l
    }
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let mut i = 0;
        while i < n {
            match self.next() {
                Some(_) => {}
                None => return None,
            }
            i += 1;
        }
        self.next()
    }
    fn fold<B, F: FnMut(B, Self::Item) -> B>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
    {
        let mut s = self;
        let mut acc = init;
        while let Some(x) = s.next() {
            acc = f(acc, x);
        }
        acc
    }
    fn for_each<F: FnMut(Self::Item)>(self, mut f: F)
    where
        Self: Sized,
    {
        let mut s = self;
        while let Some(x) = s.next() {
            f(x);
        }
    }
    fn all<F: FnMut(Self::Item) -> bool>(&mut self, mut f: F) -> bool {
        while let Some(x) = self.next() {
            if !f(x) {
                return false;
            }
        }
        true
    }
    fn sum<S: Sum<Self::Item>>(self) -> S
    where
        Self: Sized,
    {
        S::sum(self)
    }
    fn rev(self) -> Rev<Self>
    where
        Self: Sized + DoubleEndedIterator,
    {
        Rev { iter: self }
    }
    fn step_by(self, step: usize) -> StepBy<Self>
    where
        Self: Sized,
    {
        StepBy { iter: self, step }
    }
    fn take(self, n: usize) -> Take<Self>
    where
        Self: Sized,
    {
        Take { iter: self, n }
    }
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized,
    {
        Enumerate {
            iter: self,
            count: 0,
        }
    }
    fn peekable(self) -> Peekable<Self>
    where
        Self: Sized,
    {
        Peekable {
            iter: self,
            peeked: None,
        }
    }
    fn map<B, F: FnMut(Self::Item) -> B>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
    {
        Map { iter: self, f }
    }
    fn filter<P: FnMut(&Self::Item) -> bool>(self, predicate: P) -> Filter<Self, P>
    where
        Self: Sized,
    {
        Filter {
            iter: self,
            predicate,
        }
    }
    fn zip<U: IntoIterator>(self, other: U) -> Zip<Self, U::IntoIter>
    where
        Self: Sized,
    {
        Zip {
            a: self,
            b: other.into_iter(),
        }
    }
    fn chain<U: IntoIterator<Item = Self::Item>>(self, other: U) -> Chain<Self, U::IntoIter>
    where
        Self: Sized,
    {
        Chain {
            a: Some(self),
            b: Some(other.into_iter()),
        }
    }
    fn max(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        let mut s = self;
        let mut m: Option<Self::Item> = None;
        while let Some(x) = s.next() {
            m = match m {
                None => Some(x),
                Some(y) => Some(if x > y { x } else { y }),
            };
        }
        m
    }
    fn flatten(self) -> Flatten<Self>
    where
        Self: Sized,
        Self::Item: IntoIterator,
    {
        Flatten { iter: self }
    }
}
impl<I: Iterator> IntoIterator for I {
    type Item = I::Item;
    type IntoIter = I;
    fn into_iter(self) -> I {
        self
    }
}
pub struct Count {
    pub n: u32,
}
impl Iterator for Count {
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
impl DoubleEndedIterator for Count {
    fn next_back(&mut self) -> Option<u32> {
        self.next()
    }
}
impl FromIterator<u32> for u32 {
    fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> u32 {
        let mut it = iter.into_iter();
        let mut acc = 0;
        while let Some(x) = it.next() {
            acc += x;
        }
        acc
    }
}
pub fn use_collect() -> u32 {
    Count { n: 4 }.collect()
}
impl Sum<u32> for u32 {
    fn sum<I: Iterator<Item = u32>>(iter: I) -> u32 {
        let mut it = iter;
        let mut a = 0;
        while let Some(x) = it.next() {
            a += x;
        }
        a
    }
}
pub struct Rev<T> {
    iter: T,
}
impl<I: DoubleEndedIterator> Iterator for Rev<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        self.iter.next_back()
    }
}
pub struct StepBy<I> {
    iter: I,
    step: usize,
}
impl<I: Iterator> Iterator for StepBy<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        self.iter.next()
    }
}
pub struct Take<I> {
    iter: I,
    n: usize,
}
impl<I: Iterator> Iterator for Take<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            self.iter.next()
        }
    }
}
pub struct Enumerate<I> {
    iter: I,
    count: usize,
}
impl<I: Iterator> Iterator for Enumerate<I> {
    type Item = (usize, I::Item);
    fn next(&mut self) -> Option<(usize, I::Item)> {
        let a = match self.iter.next() {
            Some(a) => a,
            None => return None,
        };
        let i = self.count;
        self.count += 1;
        Some((i, a))
    }
}
pub struct Peekable<I: Iterator> {
    iter: I,
    peeked: Option<Option<I::Item>>,
}
impl<I: Iterator> Iterator for Peekable<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        match self.peeked.take() {
            Some(v) => v,
            None => self.iter.next(),
        }
    }
}
pub struct Map<I, F> {
    iter: I,
    f: F,
}
impl<B, I: Iterator, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {
    type Item = B;
    fn next(&mut self) -> Option<B> {
        match self.iter.next() {
            Some(x) => Some((self.f)(x)),
            None => None,
        }
    }
}
pub struct Filter<I, P> {
    iter: I,
    predicate: P,
}
impl<I: Iterator, P: FnMut(&I::Item) -> bool> Iterator for Filter<I, P> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        while let Some(x) = self.iter.next() {
            if (self.predicate)(&x) {
                return Some(x);
            }
        }
        None
    }
}
pub struct Zip<A, B> {
    a: A,
    b: B,
}
impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    type Item = (A::Item, B::Item);
    fn next(&mut self) -> Option<(A::Item, B::Item)> {
        let x = match self.a.next() {
            Some(x) => x,
            None => return None,
        };
        let y = match self.b.next() {
            Some(y) => y,
            None => return None,
        };
        Some((x, y))
    }
}
pub struct Chain<A, B> {
    a: Option<A>,
    b: Option<B>,
}
impl<A: Iterator, B: Iterator<Item = A::Item>> Iterator for Chain<A, B> {
    type Item = A::Item;
    fn next(&mut self) -> Option<A::Item> {
        if let Some(a) = &mut self.a {
            if let Some(x) = a.next() {
                return Some(x);
            }
            self.a = None;
        }
        match &mut self.b {
            Some(b) => b.next(),
            None => None,
        }
    }
}
pub struct Flatten<I> {
    iter: I,
}
