//@ [!lean] skip
//! A copy of the std iterator traits that are mutually defined with `Iterator`: `Iterator`,
//! `DoubleEndedIterator`, `ExactSizeIterator`, `IntoIterator`, `FromIterator`, `Extend`, `Sum` and
//! `Product`, with *every* method, stable or not, in std's order.
//!
//! The trait declarations and method signatures are copied verbatim from `core::iter::traits` at
//! rust-lang/rust 923c95cdf5ba65cea505aa2ea829f578e1506ed8 (nightly-2026-09-17, the toolchain of
//! Charon), including `const trait`, the `[const] Destruct` bounds and the
//! `#[rustc_non_const_trait_method]` markers. Dropped: the stability and diagnostic attributes,
//! which only std may use, and documentation.
//!
//! The std items these signatures use from outside `core::iter` (`Try`, `FromResidual`,
//! `Residual`, `ControlFlow`, `Ordering`, `NonZero`, `array::IntoIter`,
//! `Destruct`, `TrustedRandomAccessNoCoerce`) are std's own, not copies, except
//! `ChangeOutputType`, which std keeps crate-private (copied verbatim below).
//!
//! Where std's default method body calls a crate-private std function (`array::iter_next_chunk`,
//! `iter_compare`, …), the body is std's own, and the function is a stub at the top of this file,
//! with std's type and a dummy body. The adapter types keep std's names, parameters and bounds, and
//! have std's (crate-private) `new`; their fields and `Iterator` impls are simple. The other default
//! method bodies are written as simple loops that behave like std's, or are std's own when they
//! only use accessible APIs.
//!
//! A method that does not work is commented out, with the reason.
#![allow(dead_code, unused_variables, unused_mut, internal_features, unused_features)]
#![feature(
    const_trait_impl,
    const_destruct,
    const_precise_live_drops,
    const_try,
    const_try_residual,
    const_cmp,
    const_clone,
    rustc_attrs,
    try_trait_v2,
    try_trait_v2_residual,
    trusted_random_access,
    array_into_iter_constructors,
    maybe_uninit_array_assume_init
)]
use core::cmp::Ordering;
use core::iter::TrustedRandomAccessNoCoerce;
use core::marker::Destruct;
use core::ops::ControlFlow;
// use core::num::NonZero;  // only used by `advance_by`/`advance_back_by`, not supported
// Used by the methods that are commented out below (they mention `Try`, which is not supported):
// use core::ops::{FromResidual, Residual, Try};
//
// /// `core::ops::ChangeOutputType`, which is crate-private in std; copied from
// /// core/src/ops/try_trait.rs.
// #[allow(type_alias_bounds)]
// pub(crate) type ChangeOutputType<T: Try<Residual: Residual<V>>, V> =
//     <T::Residual as Residual<V>>::TryType;

// ---------------------------------------------------------------------------------------------
// Stubs for the crate-private std helpers that std's default method bodies call
// ---------------------------------------------------------------------------------------------
// A crate cannot call these, so each one is declared here with std's type and a dummy body, and
// the default methods below call it exactly as std does.

/// `core::array`, with stubs for its crate-private `iter_next_chunk` and `iter_next_chunk_back`
/// (core/src/array/mod.rs), so that `array::iter_next_chunk` resolves as in std.
pub(crate) mod array {
    pub use core::array::*;

    /// Stub for `core::array::iter_next_chunk`, called by `Iterator::next_chunk` (a `const` method,
    /// so this is a `const fn`).
    pub(crate) const fn iter_next_chunk<T, const N: usize>(
        iter: &mut impl [const] crate::Iterator<Item = T>,
    ) -> Result<[T; N], IntoIter<T, N>> {
        unimplemented!()
    }

    /// Stub for `core::array::iter_next_chunk_back`, called by `DoubleEndedIterator::next_chunk_back`.
    pub(crate) fn iter_next_chunk_back<T, const N: usize>(
        iter: &mut impl crate::DoubleEndedIterator<Item = T>,
    ) -> Result<[T; N], IntoIter<T, N>> {
        unimplemented!()
    }
}

/// Stub for `core::iter::traits::iterator::iter_compare` (signature copied verbatim), called by
/// `Iterator::cmp_by` and `Iterator::partial_cmp_by`.
fn iter_compare<A, B, F, T>(mut a: A, mut b: B, f: F) -> ControlFlow<T, Ordering>
where
    A: Iterator,
    B: Iterator,
    F: FnMut(A::Item, B::Item) -> ControlFlow<T>,
{
    unimplemented!()
}

// NOT SUPPORTED: its two `Iterator` clauses (`Self: Iterator` and `B: Iterator`) both become a Lean
// field named `IteratorInst`, aeneas#1051; so `Iterator::eq_by`, which calls it, is commented out too.
// /// Stub for `core::iter::traits::iterator::SpecIterEq` (declaration copied verbatim), called by
// /// `Iterator::eq_by`. std has a default impl for all iterators and a specialized one for
// /// `TrustedLen`; the stub has only the first.
// trait SpecIterEq<B: Iterator>: Iterator {
//     fn spec_iter_eq<F>(self, b: B, f: F) -> bool
//     where
//         F: FnMut(Self::Item, <B as Iterator>::Item) -> ControlFlow<()>;
// }
//
// impl<A: Iterator, B: Iterator> SpecIterEq<B> for A {
//     fn spec_iter_eq<F>(self, b: B, f: F) -> bool
//     where
//         F: FnMut(Self::Item, <B as Iterator>::Item) -> ControlFlow<()>,
//     {
//         unimplemented!()
//     }
// }

// ---------------------------------------------------------------------------------------------
// `Iterator` (core/src/iter/traits/iterator.rs)
// ---------------------------------------------------------------------------------------------

pub const trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;

    fn next_chunk<const N: usize>(
        &mut self,
    ) -> Result<[Self::Item; N], array::IntoIter<Self::Item, N>>
    where
        Self: Sized,
    {
        array::iter_next_chunk(self)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }

    fn count(self) -> usize
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Destruct,
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
        Self: Sized + [const] Destruct,
        Self::Item: [const] Destruct,
    {
        let mut s = self;
        let mut l = None;
        while let Some(x) = s.next() {
            l = Some(x);
        }
        l
    }

    // NOT SUPPORTED: `NonZero`: Aeneas extracts std's `NonZero` (and its `ZeroablePrimitive` trait) as
    // declarations that do not type-check in Lean (`ZeroablePrimitive` gets a duplicate field
    // `markerCopyInst`), so the return type of this method cannot be used.
    // fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>>
    // where
    //     Self::Item: [const] Destruct,
    // {
    //     let mut i = 0;
    //     while i < n {
    //         if let None = self.next() {
    //             // SAFETY: `i < n`
    //             return Err(unsafe { NonZero::new_unchecked(n - i) });
    //         }
    //         i += 1;
    //     }
    //     Ok(())
    // }

    fn nth(&mut self, n: usize) -> Option<Self::Item>
    where
        Self::Item: [const] Destruct,
    {
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

    #[rustc_non_const_trait_method]
    fn step_by(self, step: usize) -> StepBy<Self>
    where
        Self: Sized,
    {
        StepBy::new(self, step)
    }

    fn chain<U>(self, other: U) -> Chain<Self, U::IntoIter>
    where
        Self: Sized,
        U: [const] IntoIterator<Item = Self::Item>,
    {
        Chain::new(self, other.into_iter())
    }

    #[rustc_non_const_trait_method]
    fn zip<U>(self, other: U) -> Zip<Self, U::IntoIter>
    where
        Self: Sized,
        U: IntoIterator,
    {
        Zip::new(self, other.into_iter())
    }

    fn intersperse(self, separator: Self::Item) -> Intersperse<Self>
    where
        Self: Sized,
        Self::Item: Clone,
    {
        Intersperse::new(self, separator)
    }

    fn intersperse_with<G>(self, separator: G) -> IntersperseWith<Self, G>
    where
        Self: Sized,
        G: FnMut() -> Self::Item,
    {
        IntersperseWith::new(self, separator)
    }

    fn map<B, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B,
    {
        Map::new(self, f)
    }

    #[rustc_non_const_trait_method]
    fn for_each<F>(self, f: F)
    where
        Self: Sized,
        F: FnMut(Self::Item),
    {
        let mut s = self;
        let mut f = f;
        while let Some(x) = s.next() {
            f(x);
        }
    }

    fn filter<P>(self, predicate: P) -> Filter<Self, P>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        Filter::new(self, predicate)
    }

    fn filter_map<B, F>(self, f: F) -> FilterMap<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> Option<B>,
    {
        FilterMap::new(self, f)
    }

    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized,
    {
        Enumerate::new(self)
    }

    fn peekable(self) -> Peekable<Self>
    where
        Self: Sized,
    {
        Peekable::new(self)
    }

    fn skip_while<P>(self, predicate: P) -> SkipWhile<Self, P>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        SkipWhile::new(self, predicate)
    }

    fn take_while<P>(self, predicate: P) -> TakeWhile<Self, P>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        TakeWhile::new(self, predicate)
    }

    fn map_while<B, P>(self, predicate: P) -> MapWhile<Self, P>
    where
        Self: Sized,
        P: FnMut(Self::Item) -> Option<B>,
    {
        MapWhile::new(self, predicate)
    }

    fn skip(self, n: usize) -> Skip<Self>
    where
        Self: Sized,
    {
        Skip::new(self, n)
    }

    fn take(self, n: usize) -> Take<Self>
    where
        Self: Sized,
    {
        Take::new(self, n)
    }

    fn scan<St, B, F>(self, initial_state: St, f: F) -> Scan<Self, St, F>
    where
        Self: Sized,
        F: FnMut(&mut St, Self::Item) -> Option<B>,
    {
        Scan::new(self, initial_state, f)
    }

    #[rustc_non_const_trait_method]
    fn flat_map<U, F>(self, f: F) -> FlatMap<Self, U, F>
    where
        Self: Sized,
        U: IntoIterator,
        F: FnMut(Self::Item) -> U,
    {
        FlatMap::new(self, f)
    }

    fn flatten(self) -> Flatten<Self>
    where
        Self: Sized,
        Self::Item: IntoIterator,
    {
        Flatten::new(self)
    }

    fn map_windows<F, R, #[rustc_panics_when_zero] const N: usize>(
        self,
        f: F,
    ) -> MapWindows<Self, F, N>
    where
        Self: Sized,
        F: FnMut(&[Self::Item; N]) -> R,
    {
        MapWindows::new(self, f)
    }

    fn fuse(self) -> Fuse<Self>
    where
        Self: Sized,
    {
        Fuse::new(self)
    }

    fn inspect<F>(self, f: F) -> Inspect<Self, F>
    where
        Self: Sized,
        F: FnMut(&Self::Item),
    {
        Inspect::new(self, f)
    }

    fn by_ref(&mut self) -> &mut Self
    where
        Self: Sized,
    {
        self
    }

    #[rustc_non_const_trait_method]
    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        B::from_iter(self)
    }

    // NOT SUPPORTED: Its body needs an iterator over the outputs (std's `GenericShunt`), implemented in this
    // crate; that impl and this default method are mutually recursive, which Aeneas does not support
    // ("mixed mutually recursive definitions", aeneas#1264).
    // #[rustc_non_const_trait_method]
    // fn try_collect<B>(&mut self) -> ChangeOutputType<Self::Item, B>
    // where
    //     Self: Sized,
    //     Self::Item: Try<Residual: Residual<B>>,
    //     B: FromIterator<<Self::Item as Try>::Output>,
    // {
    //     let mut residual = None;
    //     let b = B::from_iter(GenericShunt { iter: self, residual: &mut residual });
    //     match residual {
    //         Some(r) => FromResidual::from_residual(r),
    //         None => Try::from_output(b),
    //     }
    // }

    #[rustc_non_const_trait_method]
    fn collect_into<E: Extend<Self::Item>>(self, collection: &mut E) -> &mut E
    where
        Self: Sized,
    {
        collection.extend(self);
        collection
    }

    #[rustc_non_const_trait_method]
    fn partition<B, F>(self, f: F) -> (B, B)
    where
        Self: Sized,
        B: Default + Extend<Self::Item>,
        F: FnMut(&Self::Item) -> bool,
    {
        let mut left: B = Default::default();
        let mut right: B = Default::default();
        let mut s = self;
        let mut f = f;
        while let Some(x) = s.next() {
            if f(&x) {
                left.extend_one(x)
            } else {
                right.extend_one(x)
            }
        }
        (left, right)
    }

    // NOT SUPPORTED: R1: the where-clause fixes `Self::Item` (`DoubleEndedIterator<Item = &'a mut T>` on
    // `Self`); Aeneas crashes on such a method (`SymbolicToPureTypes.translate_fun_sigs`), aeneas#1493.
    // #[rustc_non_const_trait_method]
    // fn partition_in_place<'a, T: 'a, P>(mut self, ref mut predicate: P) -> usize
    // where
    //     Self: Sized + DoubleEndedIterator<Item = &'a mut T>,
    //     P: FnMut(&T) -> bool,
    // {
    //     // Repeatedly find the first `false` and swap it with the last `true`.
    //     let mut true_count = 0;
    //     'outer: loop {
    //         let head = loop {
    //             match self.next() {
    //                 None => break 'outer,
    //                 Some(x) => {
    //                     if predicate(&*x) {
    //                         true_count += 1;
    //                     } else {
    //                         break x;
    //                     }
    //                 }
    //             }
    //         };
    //         let tail = loop {
    //             match self.next_back() {
    //                 None => break 'outer,
    //                 Some(x) => {
    //                     if predicate(&*x) {
    //                         break x;
    //                     }
    //                 }
    //             }
    //         };
    //         core::mem::swap(head, tail);
    //         true_count += 1;
    //     }
    //     true_count
    // }

    #[rustc_non_const_trait_method]
    fn is_partitioned<P>(mut self, mut predicate: P) -> bool
    where
        Self: Sized,
        P: FnMut(Self::Item) -> bool,
    {
        // Either all items test `true`, or the first `false` is followed by no more `true` items.
        let mut seen_false = false;
        while let Some(x) = self.next() {
            if predicate(x) {
                if seen_false {
                    return false;
                }
            } else {
                seen_false = true;
            }
        }
        true
    }

    // NOT SUPPORTED: `Try`: Aeneas's built-in model of `core::ops::Try` does not match this std (Aeneas: "Invalid
    // builtin information for trait decl: core::ops::try_trait::Try; expected 2 parent clauses, found
    // 1"), so no signature mentioning `Try` can be translated.
    // fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
    // where
    //     Self: Sized,
    //     F: [const] FnMut(B, Self::Item) -> R + [const] Destruct,
    //     R: [const] Try<Output = B>,
    // {
    //     let mut accum = init;
    //     while let Some(x) = self.next() {
    //         match f(accum, x).branch() {
    //             ControlFlow::Continue(c) => accum = c,
    //             ControlFlow::Break(r) => return FromResidual::from_residual(r),
    //         }
    //     }
    //     Try::from_output(accum)
    // }

    // NOT SUPPORTED: `Try`: Aeneas's built-in model of `core::ops::Try` does not match this std (Aeneas: "Invalid
    // builtin information for trait decl: core::ops::try_trait::Try; expected 2 parent clauses, found
    // 1"), so no signature mentioning `Try` can be translated.
    // #[rustc_non_const_trait_method]
    // fn try_for_each<F, R>(&mut self, f: F) -> R
    // where
    //     Self: Sized,
    //     F: FnMut(Self::Item) -> R,
    //     R: Try<Output = ()>,
    // {
    //     let mut f = f;
    //     while let Some(x) = self.next() {
    //         match f(x).branch() {
    //             ControlFlow::Continue(()) => {}
    //             ControlFlow::Break(r) => return FromResidual::from_residual(r),
    //         }
    //     }
    //     Try::from_output(())
    // }

    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized + [const] Destruct,
        F: [const] FnMut(B, Self::Item) -> B + [const] Destruct,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
            accum = f(accum, x);
        }
        accum
    }

    fn reduce<F>(mut self, f: F) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        F: [const] FnMut(Self::Item, Self::Item) -> Self::Item + [const] Destruct,
    {
        let first = match self.next() {
            Some(x) => x,
            None => return None,
        };
        Some(self.fold(first, f))
    }

    // NOT SUPPORTED: `Try`: Aeneas's built-in model of `core::ops::Try` does not match this std (Aeneas: "Invalid
    // builtin information for trait decl: core::ops::try_trait::Try; expected 2 parent clauses, found
    // 1"), so no signature mentioning `Try` can be translated.
    // fn try_reduce<R>(
    //     &mut self,
    //     f: impl [const] FnMut(Self::Item, Self::Item) -> R + [const] Destruct,
    // ) -> ChangeOutputType<R, Option<R::Output>>
    // where
    //     Self: Sized,
    //     R: [const] Try<Output = Self::Item, Residual: [const] Residual<Option<Self::Item>>>,
    // {
    //     let first = match self.next() {
    //         Some(i) => i,
    //         None => return Try::from_output(None),
    //     };
    //
    //     match self.try_fold(first, f).branch() {
    //         ControlFlow::Break(r) => FromResidual::from_residual(r),
    //         ControlFlow::Continue(i) => Try::from_output(Some(i)),
    //     }
    // }

    fn all<F>(&mut self, f: F) -> bool
    where
        Self: Sized,
        F: [const] FnMut(Self::Item) -> bool + [const] Destruct,
    {
        let mut f = f;
        while let Some(x) = self.next() {
            if !f(x) {
                return false;
            }
        }
        true
    }

    #[rustc_non_const_trait_method]
    fn any<F>(&mut self, f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        let mut f = f;
        while let Some(x) = self.next() {
            if f(x) {
                return true;
            }
        }
        false
    }

    #[rustc_non_const_trait_method]
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        let mut predicate = predicate;
        while let Some(x) = self.next() {
            if predicate(&x) {
                return Some(x);
            }
        }
        None
    }

    #[rustc_non_const_trait_method]
    fn find_map<B, F>(&mut self, f: F) -> Option<B>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> Option<B>,
    {
        let mut f = f;
        while let Some(x) = self.next() {
            match f(x) {
                Some(b) => return Some(b),
                None => {}
            }
        }
        None
    }

    // NOT SUPPORTED: `Try`: Aeneas's built-in model of `core::ops::Try` does not match this std (Aeneas: "Invalid
    // builtin information for trait decl: core::ops::try_trait::Try; expected 2 parent clauses, found
    // 1"), so no signature mentioning `Try` can be translated.
    // #[rustc_non_const_trait_method]
    // fn try_find<R>(
    //     &mut self,
    //     f: impl FnMut(&Self::Item) -> R,
    // ) -> ChangeOutputType<R, Option<Self::Item>>
    // where
    //     Self: Sized,
    //     R: Try<Output = bool, Residual: Residual<Option<Self::Item>>>,
    // {
    //     let mut f = f;
    //     while let Some(x) = self.next() {
    //         match f(&x).branch() {
    //             ControlFlow::Continue(false) => {}
    //             ControlFlow::Continue(true) => return Try::from_output(Some(x)),
    //             ControlFlow::Break(r) => return FromResidual::from_residual(r),
    //         }
    //     }
    //     Try::from_output(None)
    // }

    #[rustc_non_const_trait_method]
    fn position<P>(&mut self, predicate: P) -> Option<usize>
    where
        Self: Sized,
        P: FnMut(Self::Item) -> bool,
    {
        let mut predicate = predicate;
        let mut i = 0;
        while let Some(x) = self.next() {
            if predicate(x) {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    // NOT SUPPORTED: R2: the body calls `next_back` through the where-clause `Self: DoubleEndedIterator`,
    // and Aeneas gives that `DoubleEndedIterator`'s `Item` a new, unrelated name, so the body does
    // not type-check and is dropped ("New value doesn't have the same type as its destination"),
    // charon#1580.
    // #[rustc_non_const_trait_method]
    // fn rposition<P>(&mut self, predicate: P) -> Option<usize>
    // where
    //     P: FnMut(Self::Item) -> bool,
    //     Self: Sized + ExactSizeIterator + DoubleEndedIterator,
    // {
    //     let mut predicate = predicate;
    //     let mut i = self.len();
    //     while let Some(x) = self.next_back() {
    //         i -= 1;
    //         if predicate(x) {
    //             return Some(i);
    //         }
    //     }
    //     None
    // }

    fn max(self) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Ord + [const] Destruct,
    {
        let mut s = self;
        let mut m: Option<Self::Item> = None;
        while let Some(x) = s.next() {
            m = match m {
                None => Some(x),
                // the last maximum
                Some(y) => Some(if x >= y { x } else { y }),
            };
        }
        m
    }

    fn min(self) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Ord + [const] Destruct,
    {
        let mut s = self;
        let mut m: Option<Self::Item> = None;
        while let Some(x) = s.next() {
            m = match m {
                None => Some(x),
                // the first minimum
                Some(y) => Some(if x < y { x } else { y }),
            };
        }
        m
    }

    #[rustc_non_const_trait_method]
    fn max_by_key<B: Ord, F>(self, f: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(&Self::Item) -> B,
    {
        let mut s = self;
        let mut f = f;
        let mut best: Option<(B, Self::Item)> = None;
        while let Some(x) = s.next() {
            let k = f(&x);
            best = match best {
                None => Some((k, x)),
                Some((bk, bx)) => {
                    if k >= bk {
                        Some((k, x))
                    } else {
                        Some((bk, bx))
                    }
                }
            };
        }
        match best {
            Some((_, x)) => Some(x),
            None => None,
        }
    }

    fn max_by<F>(self, compare: F) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Destruct,
        F: [const] FnMut(&Self::Item, &Self::Item) -> Ordering + [const] Destruct,
    {
        let mut s = self;
        let mut compare = compare;
        let mut m: Option<Self::Item> = None;
        while let Some(x) = s.next() {
            m = match m {
                None => Some(x),
                Some(y) => match compare(&y, &x) {
                    Ordering::Greater => Some(y),
                    _ => Some(x),
                },
            };
        }
        m
    }

    #[rustc_non_const_trait_method]
    fn min_by_key<B: Ord, F>(self, f: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(&Self::Item) -> B,
    {
        let mut s = self;
        let mut f = f;
        let mut best: Option<(B, Self::Item)> = None;
        while let Some(x) = s.next() {
            let k = f(&x);
            best = match best {
                None => Some((k, x)),
                Some((bk, bx)) => {
                    if k < bk {
                        Some((k, x))
                    } else {
                        Some((bk, bx))
                    }
                }
            };
        }
        match best {
            Some((_, x)) => Some(x),
            None => None,
        }
    }

    fn min_by<F>(self, compare: F) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        F: [const] FnMut(&Self::Item, &Self::Item) -> Ordering + [const] Destruct,
        Self::Item: [const] Destruct,
    {
        let mut s = self;
        let mut compare = compare;
        let mut m: Option<Self::Item> = None;
        while let Some(x) = s.next() {
            m = match m {
                None => Some(x),
                Some(y) => match compare(&y, &x) {
                    Ordering::Greater => Some(x),
                    _ => Some(y),
                },
            };
        }
        m
    }

    fn rev(self) -> Rev<Self>
    where
        Self: Sized + DoubleEndedIterator,
    {
        Rev::new(self)
    }

    // NOT SUPPORTED: R1: the where-clause fixes `Self::Item` (`Iterator<Item = …>` on `Self`); Aeneas crashes on
    // such a method (internal error in `SymbolicToPureTypes.translate_fun_sigs`), aeneas#1493/#1491.
    // #[rustc_non_const_trait_method]
    // fn unzip<A, B, FromA, FromB>(self) -> (FromA, FromB)
    // where
    //     FromA: Default + Extend<A>,
    //     FromB: Default + Extend<B>,
    //     Self: Sized + Iterator<Item = (A, B)>,
    // {
    //     let mut a: FromA = Default::default();
    //     let mut b: FromB = Default::default();
    //     let mut s = self;
    //     while let Some((x, y)) = s.next() {
    //         a.extend_one(x);
    //         b.extend_one(y);
    //     }
    //     (a, b)
    // }

    // NOT SUPPORTED: R1: the where-clause fixes `Self::Item` (`Iterator<Item = …>` on `Self`); Aeneas crashes on
    // such a method (internal error in `SymbolicToPureTypes.translate_fun_sigs`), aeneas#1493/#1491.
    // fn copied<'a, T>(self) -> Copied<Self>
    // where
    //     T: Copy + 'a,
    //     Self: Sized + Iterator<Item = &'a T>,
    // {
    //     Copied { it: self }
    // }

    // NOT SUPPORTED: R1: the where-clause fixes `Self::Item` (`Iterator<Item = …>` on `Self`); Aeneas crashes on
    // such a method (internal error in `SymbolicToPureTypes.translate_fun_sigs`), aeneas#1493/#1491.
    // fn cloned<'a, T>(self) -> Cloned<Self>
    // where
    //     T: Clone + 'a,
    //     Self: Sized + Iterator<Item = &'a T>,
    // {
    //     Cloned { it: self }
    // }

    fn cycle(self) -> Cycle<Self>
    where
        Self: Sized + [const] Clone,
    {
        Cycle::new(self)
    }

    fn array_chunks<#[rustc_panics_when_zero] const N: usize>(self) -> ArrayChunks<Self, N>
    where
        Self: Sized,
    {
        ArrayChunks::new(self)
    }

    fn sum<S>(self) -> S
    where
        Self: Sized,
        S: [const] Sum<Self::Item>,
    {
        Sum::sum(self)
    }

    fn product<P>(self) -> P
    where
        Self: Sized,
        P: [const] Product<Self::Item>,
    {
        Product::product(self)
    }

    #[rustc_non_const_trait_method]
    fn cmp<I>(self, other: I) -> Ordering
    where
        I: IntoIterator<Item = Self::Item>,
        Self::Item: Ord,
        Self: Sized,
    {
        let mut a = self;
        let mut b = other.into_iter();
        loop {
            match a.next() {
                None => {
                    return match b.next() {
                        None => Ordering::Equal,
                        Some(_) => Ordering::Less,
                    }
                }
                Some(x) => match b.next() {
                    None => return Ordering::Greater,
                    Some(y) => match x.cmp(&y) {
                        Ordering::Equal => {}
                        non_eq => return non_eq,
                    },
                },
            }
        }
    }

    #[rustc_non_const_trait_method]
    fn cmp_by<I, F>(self, other: I, cmp: F) -> Ordering
    where
        Self: Sized,
        I: IntoIterator,
        F: FnMut(Self::Item, I::Item) -> Ordering,
    {
        #[inline]
        fn compare<X, Y, F>(mut cmp: F) -> impl FnMut(X, Y) -> ControlFlow<Ordering>
        where
            F: FnMut(X, Y) -> Ordering,
        {
            move |x, y| match cmp(x, y) {
                Ordering::Equal => ControlFlow::Continue(()),
                non_eq => ControlFlow::Break(non_eq),
            }
        }

        match iter_compare(self, other.into_iter(), compare(cmp)) {
            ControlFlow::Continue(ord) => ord,
            ControlFlow::Break(ord) => ord,
        }
    }

    #[rustc_non_const_trait_method]
    fn partial_cmp<I>(self, other: I) -> Option<Ordering>
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        let mut a = self;
        let mut b = other.into_iter();
        loop {
            match a.next() {
                None => {
                    return match b.next() {
                        None => Some(Ordering::Equal),
                        Some(_) => Some(Ordering::Less),
                    }
                }
                Some(x) => match b.next() {
                    None => return Some(Ordering::Greater),
                    Some(y) => match x.partial_cmp(&y) {
                        Some(Ordering::Equal) => {}
                        non_eq => return non_eq,
                    },
                },
            }
        }
    }

    #[rustc_non_const_trait_method]
    fn partial_cmp_by<I, F>(self, other: I, partial_cmp: F) -> Option<Ordering>
    where
        Self: Sized,
        I: IntoIterator,
        F: FnMut(Self::Item, I::Item) -> Option<Ordering>,
    {
        #[inline]
        fn compare<X, Y, F>(mut partial_cmp: F) -> impl FnMut(X, Y) -> ControlFlow<Option<Ordering>>
        where
            F: FnMut(X, Y) -> Option<Ordering>,
        {
            move |x, y| match partial_cmp(x, y) {
                Some(Ordering::Equal) => ControlFlow::Continue(()),
                non_eq => ControlFlow::Break(non_eq),
            }
        }

        match iter_compare(self, other.into_iter(), compare(partial_cmp)) {
            ControlFlow::Continue(ord) => Some(ord),
            ControlFlow::Break(ord) => ord,
        }
    }

    #[rustc_non_const_trait_method]
    fn eq<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialEq<I::Item>,
        Self: Sized,
    {
        let mut a = self;
        let mut b = other.into_iter();
        loop {
            match a.next() {
                None => {
                    return match b.next() {
                        None => true,
                        Some(_) => false,
                    }
                }
                Some(x) => match b.next() {
                    None => return false,
                    Some(y) => {
                        if !(x == y) {
                            return false;
                        }
                    }
                },
            }
        }
    }

    // NOT SUPPORTED: std's body calls the crate-private trait `SpecIterEq` (stubbed at the top of the
    // file, also commented out), whose two `Iterator` clauses (`Self: Iterator` and `B: Iterator`) both
    // become a Lean field named `IteratorInst` ("Field `IteratorInst` has already been declared"),
    // aeneas#1051.
    // #[rustc_non_const_trait_method]
    // fn eq_by<I, F>(self, other: I, eq: F) -> bool
    // where
    //     Self: Sized,
    //     I: IntoIterator,
    //     F: FnMut(Self::Item, I::Item) -> bool,
    // {
    //     #[inline]
    //     fn compare<X, Y, F>(mut eq: F) -> impl FnMut(X, Y) -> ControlFlow<()>
    //     where
    //         F: FnMut(X, Y) -> bool,
    //     {
    //         move |x, y| {
    //             if eq(x, y) { ControlFlow::Continue(()) } else { ControlFlow::Break(()) }
    //         }
    //     }
    //
    //     SpecIterEq::spec_iter_eq(self, other.into_iter(), compare(eq))
    // }

    #[rustc_non_const_trait_method]
    fn ne<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialEq<I::Item>,
        Self: Sized,
    {
        !self.eq(other)
    }

    #[rustc_non_const_trait_method]
    fn lt<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        match self.partial_cmp(other) {
            Some(Ordering::Less) => true,
            _ => false,
        }
    }

    #[rustc_non_const_trait_method]
    fn le<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        match self.partial_cmp(other) {
            Some(Ordering::Less | Ordering::Equal) => true,
            _ => false,
        }
    }

    #[rustc_non_const_trait_method]
    fn gt<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        match self.partial_cmp(other) {
            Some(Ordering::Greater) => true,
            _ => false,
        }
    }

    #[rustc_non_const_trait_method]
    fn ge<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        match self.partial_cmp(other) {
            Some(Ordering::Greater | Ordering::Equal) => true,
            _ => false,
        }
    }

    fn is_sorted(self) -> bool
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] PartialOrd + [const] Destruct,
    {
        let mut s = self;
        let mut last = match s.next() {
            Some(e) => e,
            None => return true,
        };
        while let Some(curr) = s.next() {
            if !(last <= curr) {
                return false;
            }
            last = curr;
        }
        true
    }

    fn is_sorted_by<F>(mut self, compare: F) -> bool
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Destruct,
        F: [const] FnMut(&Self::Item, &Self::Item) -> bool + [const] Destruct,
    {
        let mut compare = compare;
        let mut last = match self.next() {
            Some(e) => e,
            None => return true,
        };
        while let Some(curr) = self.next() {
            if !compare(&last, &curr) {
                return false;
            }
            last = curr;
        }
        true
    }

    #[rustc_non_const_trait_method]
    fn is_sorted_by_key<F, K>(self, f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> K,
        K: PartialOrd,
    {
        let mut s = self;
        let mut f = f;
        let mut last = match s.next() {
            Some(e) => f(e),
            None => return true,
        };
        while let Some(x) = s.next() {
            let curr = f(x);
            if !(last <= curr) {
                return false;
            }
            last = curr;
        }
        true
    }

    #[doc(hidden)]
    unsafe fn __iterator_get_unchecked(&mut self, _idx: usize) -> Self::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // std: `unreachable!("Always specialized")`, which is const only inside `core`
        panic!("internal error: entered unreachable code: Always specialized");
    }
}

// ---------------------------------------------------------------------------------------------
// `DoubleEndedIterator` (core/src/iter/traits/double_ended.rs)
// ---------------------------------------------------------------------------------------------

pub const trait DoubleEndedIterator: [const] Iterator {
    fn next_back(&mut self) -> Option<Self::Item>;

    #[rustc_non_const_trait_method]
    fn next_chunk_back<const N: usize>(
        &mut self,
    ) -> Result<[Self::Item; N], array::IntoIter<Self::Item, N>>
    where
        Self: Sized,
    {
        crate::array::iter_next_chunk_back(self)
    }

    // NOT SUPPORTED: `NonZero`: Aeneas extracts std's `NonZero` (and its `ZeroablePrimitive` trait) as
    // declarations that do not type-check in Lean (`ZeroablePrimitive` gets a duplicate field
    // `markerCopyInst`), so the return type of this method cannot be used.
    // fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>>
    // where
    //     Self::Item: [const] Destruct,
    // {
    //     let mut i = 0;
    //     while i < n {
    //         if let None = self.next_back() {
    //             // SAFETY: `i < n`
    //             return Err(unsafe { NonZero::new_unchecked(n - i) });
    //         }
    //         i += 1;
    //     }
    //     Ok(())
    // }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item>
    where
        Self::Item: [const] Destruct,
    {
        let mut i = 0;
        while i < n {
            match self.next_back() {
                Some(_) => {}
                None => return None,
            }
            i += 1;
        }
        self.next_back()
    }

    // NOT SUPPORTED: `Try`: Aeneas's built-in model of `core::ops::Try` does not match this std (Aeneas: "Invalid
    // builtin information for trait decl: core::ops::try_trait::Try; expected 2 parent clauses, found
    // 1"), so no signature mentioning `Try` can be translated.
    // fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
    // where
    //     Self: Sized,
    //     F: [const] FnMut(B, Self::Item) -> R + [const] Destruct,
    //     R: [const] Try<Output = B>,
    // {
    //     let mut accum = init;
    //     while let Some(x) = self.next_back() {
    //         match f(accum, x).branch() {
    //             ControlFlow::Continue(c) => accum = c,
    //             ControlFlow::Break(r) => return FromResidual::from_residual(r),
    //         }
    //     }
    //     Try::from_output(accum)
    // }

    fn rfold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized + [const] Destruct,
        F: [const] FnMut(B, Self::Item) -> B + [const] Destruct,
    {
        let mut accum = init;
        while let Some(x) = self.next_back() {
            accum = f(accum, x);
        }
        accum
    }

    fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        Self: Sized,
        P: [const] FnMut(&Self::Item) -> bool + [const] Destruct,
        Self::Item: [const] Destruct,
    {
        let mut predicate = predicate;
        while let Some(x) = self.next_back() {
            if predicate(&x) {
                return Some(x);
            }
        }
        None
    }
}

// ---------------------------------------------------------------------------------------------
// `ExactSizeIterator` (core/src/iter/traits/exact_size.rs)
// ---------------------------------------------------------------------------------------------

pub trait ExactSizeIterator: Iterator {
    fn len(&self) -> usize {
        let (lower, upper) = self.size_hint();
        // Note: This assertion is overly defensive, but it checks the invariant
        // guaranteed by the trait. If this trait were rust-internal,
        // we could use debug_assert!; assert_eq! will check all Rust user
        // implementations too.
        assert_eq!(upper, Some(lower));
        lower
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// ---------------------------------------------------------------------------------------------
// `IntoIterator`, `FromIterator`, `Extend` (core/src/iter/traits/collect.rs)
// ---------------------------------------------------------------------------------------------

pub const trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;
    fn into_iter(self) -> Self::IntoIter;
}

pub trait FromIterator<T>: Sized {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self;
}

const impl<I: [const] Iterator> IntoIterator for I {
    type Item = I::Item;
    type IntoIter = I;

    #[inline]
    fn into_iter(self) -> I {
        self
    }
}

pub trait Extend<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I);

    fn extend_one(&mut self, item: T) {
        self.extend(Some(item));
    }

    fn extend_reserve(&mut self, additional: usize) {
        let _ = additional;
    }

    #[doc(hidden)]
    unsafe fn extend_one_unchecked(&mut self, item: T)
    where
        Self: Sized,
    {
        self.extend_one(item);
    }
}

// ---------------------------------------------------------------------------------------------
// `Sum`, `Product` (core/src/iter/traits/accum.rs)
// ---------------------------------------------------------------------------------------------

pub const trait Sum<A = Self>: Sized {
    fn sum<I: Iterator<Item = A>>(iter: I) -> Self;
}

pub const trait Product<A = Self>: Sized {
    fn product<I: Iterator<Item = A>>(iter: I) -> Self;
}

// ---------------------------------------------------------------------------------------------
// The `Option` iterator, which std's `Extend::extend_one` default extends with
// (core/src/option.rs: `impl<T> IntoIterator for Option<T>`, iterating with `option::IntoIter`)
// ---------------------------------------------------------------------------------------------

pub struct OptionIntoIter<A> {
    inner: Option<A>,
}
impl<A> Iterator for OptionIntoIter<A> {
    type Item = A;
    fn next(&mut self) -> Option<A> {
        self.inner.take()
    }
}
impl<T> IntoIterator for Option<T> {
    type Item = T;
    type IntoIter = OptionIntoIter<T>;
    fn into_iter(self) -> OptionIntoIter<T> {
        OptionIntoIter { inner: self }
    }
}

// ---------------------------------------------------------------------------------------------
// The adapters (core/src/iter/adapters), with std's names, parameters and bounds
// ---------------------------------------------------------------------------------------------

// Not used: `try_collect` (its only user) is not supported.
// /// The iterator `try_collect` collects from: the outputs, until the first residual.
// pub struct GenericShunt<'a, I, R> {
//     iter: &'a mut I,
//     residual: &'a mut Option<R>,
// }
// impl<'a, I: Iterator, R> Iterator for GenericShunt<'a, I, R>
// where
//     I::Item: Try<Residual = R>,
// {
//     type Item = <I::Item as Try>::Output;
//     fn next(&mut self) -> Option<Self::Item> {
//         match self.iter.next() {
//             None => None,
//             Some(x) => match x.branch() {
//                 ControlFlow::Continue(o) => Some(o),
//                 ControlFlow::Break(r) => {
//                     *self.residual = Some(r);
//                     None
//                 }
//             },
//         }
//     }
// }

pub struct StepBy<I> {
    iter: I,
    step_minus_one: usize,
    first_take: bool,
}
// std's `new` (crate-private there), with the fields above.
impl<I> StepBy<I> {
    pub(crate) fn new(iter: I, step: usize) -> StepBy<I> {
        assert!(step != 0);
        StepBy { iter, step_minus_one: step - 1, first_take: true }
    }
}
impl<I: Iterator> Iterator for StepBy<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        if self.first_take {
            self.first_take = false;
            self.iter.next()
        } else {
            self.iter.nth(self.step_minus_one)
        }
    }
}

pub struct Chain<A, B> {
    a: Option<A>,
    b: Option<B>,
}
// std's `new` (crate-private there), with the fields above.
impl<A, B> Chain<A, B> {
    pub(crate) const fn new(a: A, b: B) -> Chain<A, B> {
        Chain { a: Some(a), b: Some(b) }
    }
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

pub struct Zip<A, B> {
    a: A,
    b: B,
}
// std's `new` (crate-private there), with the fields above.
impl<A: Iterator, B: Iterator> Zip<A, B> {
    pub(crate) fn new(a: A, b: B) -> Zip<A, B> {
        Zip { a, b }
    }
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

pub struct Intersperse<I: Iterator>
where
    I::Item: Clone,
{
    started: bool,
    separator: I::Item,
    next_item: Option<I::Item>,
    iter: I,
}
// std's `new` (crate-private there), with the fields above.
impl<I: Iterator> Intersperse<I>
where
    I::Item: Clone,
{
    pub(crate) const fn new(iter: I, separator: I::Item) -> Self {
        Self { started: false, separator, next_item: None, iter }
    }
}
impl<I: Iterator> Iterator for Intersperse<I>
where
    I::Item: Clone,
{
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        if self.started {
            match self.next_item.take() {
                Some(v) => Some(v),
                None => match self.iter.next() {
                    Some(x) => {
                        self.next_item = Some(x);
                        Some(self.separator.clone())
                    }
                    None => None,
                },
            }
        } else {
            self.started = true;
            self.iter.next()
        }
    }
}

pub struct IntersperseWith<I, G>
where
    I: Iterator,
{
    started: bool,
    separator: G,
    next_item: Option<I::Item>,
    iter: I,
}
// std's `new` (crate-private there), with the fields above.
impl<I, G> IntersperseWith<I, G>
where
    I: Iterator,
    G: FnMut() -> I::Item,
{
    pub(crate) const fn new(iter: I, separator: G) -> Self {
        Self { started: false, separator, next_item: None, iter }
    }
}
impl<I: Iterator, G: FnMut() -> I::Item> Iterator for IntersperseWith<I, G> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        if self.started {
            match self.next_item.take() {
                Some(v) => Some(v),
                None => match self.iter.next() {
                    Some(x) => {
                        self.next_item = Some(x);
                        Some((self.separator)())
                    }
                    None => None,
                },
            }
        } else {
            self.started = true;
            self.iter.next()
        }
    }
}

pub struct Map<I, F> {
    iter: I,
    f: F,
}
// std's `new` (crate-private there), with the fields above.
impl<I, F> Map<I, F> {
    pub(crate) const fn new(iter: I, f: F) -> Map<I, F> {
        Map { iter, f }
    }
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
// std's `new` (crate-private there), with the fields above.
impl<I, P> Filter<I, P> {
    pub(crate) const fn new(iter: I, predicate: P) -> Filter<I, P> {
        Filter { iter, predicate }
    }
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

pub struct FilterMap<I, F> {
    iter: I,
    f: F,
}
// std's `new` (crate-private there), with the fields above.
impl<I, F> FilterMap<I, F> {
    pub(crate) const fn new(iter: I, f: F) -> FilterMap<I, F> {
        FilterMap { iter, f }
    }
}
impl<B, I: Iterator, F: FnMut(I::Item) -> Option<B>> Iterator for FilterMap<I, F> {
    type Item = B;
    fn next(&mut self) -> Option<B> {
        while let Some(x) = self.iter.next() {
            match (self.f)(x) {
                Some(y) => return Some(y),
                None => {}
            }
        }
        None
    }
}

pub struct Enumerate<I> {
    iter: I,
    count: usize,
}
// std's `new` (crate-private there), with the fields above.
impl<I> Enumerate<I> {
    pub(crate) const fn new(iter: I) -> Enumerate<I> {
        Enumerate { iter, count: 0 }
    }
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
// std's `new` (crate-private there), with the fields above.
impl<I: Iterator> Peekable<I> {
    pub(crate) const fn new(iter: I) -> Peekable<I> {
        Peekable { iter, peeked: None }
    }
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

pub struct SkipWhile<I, P> {
    iter: I,
    flag: bool,
    predicate: P,
}
// std's `new` (crate-private there), with the fields above.
impl<I, P> SkipWhile<I, P> {
    pub(crate) const fn new(iter: I, predicate: P) -> SkipWhile<I, P> {
        SkipWhile { iter, flag: false, predicate }
    }
}
impl<I: Iterator, P: FnMut(&I::Item) -> bool> Iterator for SkipWhile<I, P> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        while let Some(x) = self.iter.next() {
            if self.flag || !(self.predicate)(&x) {
                self.flag = true;
                return Some(x);
            }
        }
        None
    }
}

pub struct TakeWhile<I, P> {
    iter: I,
    flag: bool,
    predicate: P,
}
// std's `new` (crate-private there), with the fields above.
impl<I, P> TakeWhile<I, P> {
    pub(crate) const fn new(iter: I, predicate: P) -> TakeWhile<I, P> {
        TakeWhile { iter, flag: false, predicate }
    }
}
impl<I: Iterator, P: FnMut(&I::Item) -> bool> Iterator for TakeWhile<I, P> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        if self.flag {
            return None;
        }
        match self.iter.next() {
            Some(x) => {
                if (self.predicate)(&x) {
                    Some(x)
                } else {
                    self.flag = true;
                    None
                }
            }
            None => None,
        }
    }
}

pub struct MapWhile<I, P> {
    iter: I,
    predicate: P,
}
// std's `new` (crate-private there), with the fields above.
impl<I, P> MapWhile<I, P> {
    pub(crate) const fn new(iter: I, predicate: P) -> MapWhile<I, P> {
        MapWhile { iter, predicate }
    }
}
impl<B, I: Iterator, P: FnMut(I::Item) -> Option<B>> Iterator for MapWhile<I, P> {
    type Item = B;
    fn next(&mut self) -> Option<B> {
        match self.iter.next() {
            Some(x) => (self.predicate)(x),
            None => None,
        }
    }
}

pub struct Skip<I> {
    iter: I,
    n: usize,
}
// std's `new` (crate-private there), with the fields above.
impl<I> Skip<I> {
    pub(crate) const fn new(iter: I, n: usize) -> Skip<I> {
        Skip { iter, n }
    }
}
impl<I: Iterator> Iterator for Skip<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        while self.n > 0 {
            self.n -= 1;
            match self.iter.next() {
                Some(_) => {}
                None => return None,
            }
        }
        self.iter.next()
    }
}

pub struct Take<I> {
    iter: I,
    n: usize,
}
// std's `new` (crate-private there), with the fields above.
impl<I> Take<I> {
    pub(crate) const fn new(iter: I, n: usize) -> Take<I> {
        Take { iter, n }
    }
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

pub struct Scan<I, St, F> {
    iter: I,
    f: F,
    state: St,
}
// std's `new` (crate-private there), with the fields above.
impl<I, St, F> Scan<I, St, F> {
    pub(crate) const fn new(iter: I, state: St, f: F) -> Scan<I, St, F> {
        Scan { iter, state, f }
    }
}
// NOT SUPPORTED: the impl's `next` calls the closure, whose argument type contains `&mut St`;
// Aeneas models `&mut` inside the generic `Args` of `FnMut` as a plain value, so `call_mut` cannot
// return the updated state that the body needs (aeneas#961, #1215). (`Iterator::scan` itself is fine.)
// impl<B, I: Iterator, St, F: FnMut(&mut St, I::Item) -> Option<B>> Iterator for Scan<I, St, F> {
//     type Item = B;
//     fn next(&mut self) -> Option<B> {
//         match self.iter.next() {
//             Some(a) => (self.f)(&mut self.state, a),
//             None => None,
//         }
//     }
// }

pub struct FlatMap<I, U: IntoIterator, F> {
    iter: I,
    f: F,
    frontiter: Option<U::IntoIter>,
}
// std's `new` (crate-private there), with the fields above.
impl<I: Iterator, U: IntoIterator, F: FnMut(I::Item) -> U> FlatMap<I, U, F> {
    pub(crate) fn new(iter: I, f: F) -> FlatMap<I, U, F> {
        FlatMap { iter, f, frontiter: None }
    }
}
impl<I: Iterator, U: IntoIterator, F: FnMut(I::Item) -> U> Iterator for FlatMap<I, U, F> {
    type Item = U::Item;
    fn next(&mut self) -> Option<U::Item> {
        loop {
            if let Some(inner) = &mut self.frontiter {
                match inner.next() {
                    Some(x) => return Some(x),
                    None => self.frontiter = None,
                }
            }
            match self.iter.next() {
                Some(x) => self.frontiter = Some((self.f)(x).into_iter()),
                None => return None,
            }
        }
    }
}

pub struct Flatten<I: Iterator<Item: IntoIterator>> {
    iter: I,
    frontiter: Option<<I::Item as IntoIterator>::IntoIter>,
}
// std's `new` (crate-private there), with the fields above.
const impl<I: [const] Iterator<Item: IntoIterator>> Flatten<I> {
    pub(crate) fn new(iter: I) -> Flatten<I> {
        Flatten { iter, frontiter: None }
    }
}
impl<I: Iterator<Item: IntoIterator>> Iterator for Flatten<I> {
    type Item = <I::Item as IntoIterator>::Item;
    fn next(&mut self) -> Option<<I::Item as IntoIterator>::Item> {
        loop {
            if let Some(inner) = &mut self.frontiter {
                match inner.next() {
                    Some(x) => return Some(x),
                    None => self.frontiter = None,
                }
            }
            match self.iter.next() {
                Some(x) => self.frontiter = Some(x.into_iter()),
                None => return None,
            }
        }
    }
}

/// No `Iterator` impl: std's keeps a sliding window buffer of `N` items.
pub struct MapWindows<I: Iterator, F, const N: usize> {
    iter: Option<I>,
    f: F,
    buffer: Option<[I::Item; N]>,
}
// std's `new` (crate-private there), with the fields above.
impl<I: Iterator, F, const N: usize> MapWindows<I, F, N> {
    pub(crate) const fn new(iter: I, f: F) -> Self {
        assert!(N != 0, "array in `Iterator::map_windows` must contain more than 0 elements");
        Self { iter: Some(iter), f, buffer: None }
    }
}

pub struct Fuse<I> {
    iter: Option<I>,
}
// std's `new` (crate-private there), with the fields above.
impl<I> Fuse<I> {
    pub(crate) const fn new(iter: I) -> Fuse<I> {
        Fuse { iter: Some(iter) }
    }
}
impl<I: Iterator> Iterator for Fuse<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        match &mut self.iter {
            Some(it) => match it.next() {
                Some(x) => Some(x),
                None => {
                    self.iter = None;
                    None
                }
            },
            None => None,
        }
    }
}

pub struct Inspect<I, F> {
    iter: I,
    f: F,
}
// std's `new` (crate-private there), with the fields above.
impl<I, F> Inspect<I, F> {
    pub(crate) const fn new(iter: I, f: F) -> Inspect<I, F> {
        Inspect { iter, f }
    }
}
impl<I: Iterator, F: FnMut(&I::Item)> Iterator for Inspect<I, F> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        match self.iter.next() {
            Some(x) => {
                (self.f)(&x);
                Some(x)
            }
            None => None,
        }
    }
}

pub struct Rev<T> {
    iter: T,
}
// std's `new` (crate-private there), with the fields above.
impl<T> Rev<T> {
    pub(crate) const fn new(iter: T) -> Rev<T> {
        Rev { iter }
    }
}
impl<I: DoubleEndedIterator> Iterator for Rev<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        self.iter.next_back()
    }
}

pub struct Copied<I> {
    it: I,
}
impl<'a, I: Iterator<Item = &'a T>, T: 'a + Copy> Iterator for Copied<I> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        match self.it.next() {
            Some(x) => Some(*x),
            None => None,
        }
    }
}

pub struct Cloned<I> {
    it: I,
}
impl<'a, I: Iterator<Item = &'a T>, T: 'a + Clone> Iterator for Cloned<I> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        match self.it.next() {
            Some(x) => Some(x.clone()),
            None => None,
        }
    }
}

pub struct Cycle<I> {
    orig: I,
    iter: I,
}
// std's `new` (crate-private there), with the fields above.
const impl<I: [const] Clone> Cycle<I> {
    pub(crate) fn new(iter: I) -> Cycle<I> {
        Cycle { orig: iter.clone(), iter }
    }
}
impl<I: Clone + Iterator> Iterator for Cycle<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        match self.iter.next() {
            None => {
                self.iter = self.orig.clone();
                self.iter.next()
            }
            y => y,
        }
    }
}

/// No `Iterator` impl: std's collects `N` items into an array, with `next_chunk`.
pub struct ArrayChunks<I: Iterator, const N: usize> {
    iter: I,
    remainder: Option<array::IntoIter<I::Item, N>>,
}
// std's `new` (crate-private there), with the fields above.
impl<I, const N: usize> ArrayChunks<I, N>
where
    I: Iterator,
{
    #[track_caller]
    pub(crate) const fn new(iter: I) -> Self {
        assert!(N != 0, "chunk size must be non-zero");
        Self { iter, remainder: None }
    }
}

// std's impls of `Iterator` and `ExactSizeIterator` for `&mut I` (the ones `by_ref` is for):
// impl<I: Iterator + ?Sized> Iterator for &mut I { … }
// impl<I: ExactSizeIterator + ?Sized> ExactSizeIterator for &mut I { … }

// ---------------------------------------------------------------------------------------------
// A small iterator, using the traits
// ---------------------------------------------------------------------------------------------

#[derive(Clone)]
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
impl ExactSizeIterator for Count {}
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
pub fn use_collect() -> u32 {
    Count { n: 4 }.collect()
}
