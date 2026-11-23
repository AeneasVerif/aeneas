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
//! The default method bodies are std's own, verbatim. Where one uses a crate-private std item
//! (`array::iter_next_chunk`, `iter_compare`, `try_process`, …), the item is a stub at the top of
//! this file, with std's type and a dummy body, or a copy (`ChangeOutputType`, `KeyAndValue`).
//! The adapter types keep std's names, parameters and bounds, and have std's (crate-private) `new`;
//! their fields and `Iterator` impls are simple.
//!
//! A method that does not work is commented out (`/* … */`, so that its text is std's), with the
//! reason; so is a method whose body calls one that is commented out.
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
    maybe_uninit_array_assume_init,
    const_closures,
    try_blocks,
    specialization,
    const_iter,
    const_control_flow,
    const_result_trait_fn,
    // std's method bodies contain stability attributes, which need these two
    staged_api
)]
#![unstable(feature = "nonpos_iterator", issue = "none")]
use core::cmp::{self, Ordering};
use core::iter::TrustedRandomAccessNoCoerce;
use core::marker::Destruct;
use core::mem;
use core::num::NonZero;
use core::ops::{ControlFlow, FromResidual, Residual, Try};

// Used only by the methods that mention `Try`, which are commented out (see `try_fold`).
/*
/// `core::ops::ChangeOutputType`, which is crate-private in std; copied from
/// core/src/ops/try_trait.rs.
#[allow(type_alias_bounds)]
pub(crate) type ChangeOutputType<T: Try<Residual: Residual<V>>, V> =
    <T::Residual as Residual<V>>::TryType;
*/

/// `core::cmp::KeyAndValue`, which is crate-private in std; copied from core/src/cmp.rs.
#[derive(Debug, Copy, Clone)]
pub(crate) struct KeyAndValue<K, V> {
    pub key: K,
    pub value: V,
}
impl<K: PartialEq, V> PartialEq for KeyAndValue<K, V> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
    #[inline]
    fn ne(&self, other: &Self) -> bool {
        self.key != other.key
    }
}
impl<K: Eq, V> Eq for KeyAndValue<K, V> {}
impl<K: PartialOrd, V> PartialOrd for KeyAndValue<K, V> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        PartialOrd::partial_cmp(&self.key, &other.key)
    }
    #[inline]
    fn lt(&self, other: &Self) -> bool {
        self.key < other.key
    }
    #[inline]
    fn le(&self, other: &Self) -> bool {
        self.key <= other.key
    }
    #[inline]
    fn gt(&self, other: &Self) -> bool {
        self.key > other.key
    }
    #[inline]
    fn ge(&self, other: &Self) -> bool {
        self.key >= other.key
    }
}
impl<K: Ord, V> Ord for KeyAndValue<K, V> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&self.key, &other.key)
    }
}

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

// Used only by `Iterator::try_collect`, which is commented out.
/*
/// Stub for `core::iter::adapters::try_process` (signature copied verbatim), called by
/// `Iterator::try_collect`.
pub(crate) fn try_process<I, T, R, F, U>(iter: I, mut f: F) -> ChangeOutputType<I::Item, U>
where
    I: Iterator<Item: Try<Output = T, Residual = R>>,
    for<'a> F: FnMut(GenericShunt<'a, I, R>) -> U,
    R: Residual<U>,
{
    unimplemented!()
}
*/

// Used only by `Iterator::eq_by`, which is commented out.
/*
/// Stub for `core::iter::traits::iterator::SpecIterEq` (declaration copied verbatim), called by
/// `Iterator::eq_by`. std has a default impl for all iterators and a specialized one for
/// `TrustedLen`; the stub has only the first.
trait SpecIterEq<B: Iterator>: Iterator {
    fn spec_iter_eq<F>(self, b: B, f: F) -> bool
    where
        F: FnMut(Self::Item, <B as Iterator>::Item) -> ControlFlow<()>;
}

impl<A: Iterator, B: Iterator> SpecIterEq<B> for A {
    fn spec_iter_eq<F>(self, b: B, f: F) -> bool
    where
        F: FnMut(Self::Item, <B as Iterator>::Item) -> ControlFlow<()>,
    {
        unimplemented!()
    }
}
*/

// ---------------------------------------------------------------------------------------------
// `Iterator` (core/src/iter/traits/iterator.rs)
// ---------------------------------------------------------------------------------------------

#[rustc_const_unstable(feature = "const_iter", issue = "92476")]
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
        self.fold(
            0,
            #[rustc_inherit_overflow_checks]
            const |accum, _elem| accum + 1,
        )
    }

    // NOT SUPPORTED: its body defines a function named `some`, which in Lean shadows `Option.some`, so the
    // generated code does not type-check.
    /*
    fn last(self) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Destruct,
    {
        #[inline]
        #[rustc_const_unstable(feature = "const_destruct", issue = "133214")]
        const fn some<T>(_: Option<T>, x: T) -> Option<T>
        where
            T: [const] Destruct,
        {
            Some(x)
        }

        self.fold(None, some)
    }
    */

    // NOT SUPPORTED: its body calls `try_fold`, which is commented out.
    /*
    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>>
    where
        Self::Item: [const] Destruct,
    {
        /// Helper trait to specialize `advance_by` via `try_fold` for `Sized` iterators.

        #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
        const trait SpecAdvanceBy {
            fn spec_advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>>;
        }

        #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
        const impl<I: [const] Iterator + ?Sized> SpecAdvanceBy for I
        where
            I::Item: [const] Destruct,
        {
            default fn spec_advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
                for i in 0..n {
                    if self.next().is_none() {
                        // SAFETY: `i` is always less than `n`.
                        return Err(unsafe { NonZero::new_unchecked(n - i) });
                    }
                }
                Ok(())
            }
        }

        #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
        const impl<I: [const] Iterator> SpecAdvanceBy for I
        where
            I::Item: [const] Destruct,
        {
            fn spec_advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
                let Some(n) = NonZero::new(n) else {
                    return Ok(());
                };

                let res = self.try_fold(n, const |n, _| NonZero::new(n.get() - 1));

                match res {
                    None => Ok(()),
                    Some(n) => Err(n),
                }
            }
        }

        self.spec_advance_by(n)
    }
    */

    // NOT SUPPORTED: its body calls `advance_by`, which is commented out.
    /*
    fn nth(&mut self, n: usize) -> Option<Self::Item>
    where
        Self::Item: [const] Destruct,
    {
        self.advance_by(n).ok()?;
        self.next()
    }
    */

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

    // NOT SUPPORTED: its closure returns `()`, and Aeneas generates an ill-typed `call_mut` for it (the
    // unit output is dropped).
    /*
    #[rustc_non_const_trait_method]
    fn for_each<F>(self, f: F)
    where
        Self: Sized,
        F: FnMut(Self::Item),
    {
        #[inline]
        fn call<T>(mut f: impl FnMut(T)) -> impl FnMut((), T) {
            move |(), item| f(item)
        }

        self.fold((), call(f));
    }
    */

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

    // NOT SUPPORTED: its body calls `Option::is_none_or`, which Aeneas does not model (an axiom), with a
    // closure that carries the dictionary, so its continuity cannot be proved.
    /*
    #[rustc_non_const_trait_method]
    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        // This is too aggressive to turn on for everything all the time, but PR#137908
        // accidentally noticed that some rustc iterators had malformed `size_hint`s,
        // so this will help catch such things in debug-assertions-std runners,
        // even if users won't actually ever see it.
        if cfg!(debug_assertions) {
            let hint = self.size_hint();
            assert!(hint.1.is_none_or(|high| high >= hint.0), "Malformed size_hint {hint:?}");
        }

        FromIterator::from_iter(self)
    }
    */

    // NOT SUPPORTED: its body uses `GenericShunt` and `ByRefSized`, whose `Iterator` impls are then mutually
    // recursive with this method, aeneas#1264.
    /*
    #[rustc_non_const_trait_method]
    fn try_collect<B>(&mut self) -> ChangeOutputType<Self::Item, B>
    where
        Self: Sized,
        Self::Item: Try<Residual: Residual<B>>,
        B: FromIterator<<Self::Item as Try>::Output>,
    {
        try_process(ByRefSized(self), |i| i.collect())
    }
    */

    #[rustc_non_const_trait_method]
    fn collect_into<E: Extend<Self::Item>>(self, collection: &mut E) -> &mut E
    where
        Self: Sized,
    {
        collection.extend(self);
        collection
    }

    // NOT SUPPORTED: its closure captures `&mut` variables, and Aeneas generates an ill-typed
    // `call_mut`/`call_once` for it.
    /*
    #[rustc_non_const_trait_method]
    fn partition<B, F>(self, f: F) -> (B, B)
    where
        Self: Sized,
        B: Default + Extend<Self::Item>,
        F: FnMut(&Self::Item) -> bool,
    {
        #[inline]
        fn extend<'a, T, B: Extend<T>>(
            mut f: impl FnMut(&T) -> bool + 'a,
            left: &'a mut B,
            right: &'a mut B,
        ) -> impl FnMut((), T) + 'a {
            move |(), x| {
                if f(&x) {
                    left.extend_one(x);
                } else {
                    right.extend_one(x);
                }
            }
        }

        let mut left: B = Default::default();
        let mut right: B = Default::default();

        self.fold((), extend(f, &mut left, &mut right));

        (left, right)
    }
    */

    // NOT SUPPORTED: its body calls `find` and `rfind`, which are commented out.
    /*
    #[rustc_non_const_trait_method]
    fn partition_in_place<'a, T: 'a, P>(mut self, ref mut predicate: P) -> usize
    where
        Self: Sized + DoubleEndedIterator<Item = &'a mut T>,
        P: FnMut(&T) -> bool,
    {
        // FIXME: should we worry about the count overflowing? The only way to have more than
        // `usize::MAX` mutable references is with ZSTs, which aren't useful to partition...

        // These closure "factory" functions exist to avoid genericity in `Self`.

        #[inline]
        fn is_false<'a, T>(
            predicate: &'a mut impl FnMut(&T) -> bool,
            true_count: &'a mut usize,
        ) -> impl FnMut(&&mut T) -> bool + 'a {
            move |x| {
                let p = predicate(&**x);
                *true_count += p as usize;
                !p
            }
        }

        #[inline]
        fn is_true<T>(predicate: &mut impl FnMut(&T) -> bool) -> impl FnMut(&&mut T) -> bool + '_ {
            move |x| predicate(&**x)
        }

        // Repeatedly find the first `false` and swap it with the last `true`.
        let mut true_count = 0;
        while let Some(head) = self.find(is_false(predicate, &mut true_count)) {
            if let Some(tail) = self.rfind(is_true(predicate)) {
                crate::mem::swap(head, tail);
                true_count += 1;
            } else {
                break;
            }
        }
        true_count
    }
    */

    // NOT SUPPORTED: its body calls `all` and `any`, which are commented out.
    /*
    #[rustc_non_const_trait_method]
    fn is_partitioned<P>(mut self, mut predicate: P) -> bool
    where
        Self: Sized,
        P: FnMut(Self::Item) -> bool,
    {
        // Either all items test `true`, or the first clause stops at `false`
        // and we check that there are no more `true` items after that.
        self.all(&mut predicate) || !self.any(predicate)
    }
    */

    // NOT SUPPORTED: Aeneas crashes on a where-clause fixing an associated type (`R: Try<Output = …>`),
    // aeneas#1493.
    /*
    fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: [const] FnMut(B, Self::Item) -> R + [const] Destruct,
        R: [const] Try<Output = B>,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
            accum = f(accum, x)?;
        }
        try { accum }
    }
    */

    // NOT SUPPORTED: Aeneas crashes on a where-clause fixing an associated type (`R: Try<Output = …>`),
    // aeneas#1493.
    /*
    #[rustc_non_const_trait_method]
    fn try_for_each<F, R>(&mut self, f: F) -> R
    where
        Self: Sized,
        F: FnMut(Self::Item) -> R,
        R: Try<Output = ()>,
    {
        #[inline]
        fn call<T, R>(mut f: impl FnMut(T) -> R) -> impl FnMut((), T) -> R {
            move |(), x| f(x)
        }

        self.try_fold((), call(f))
    }
    */

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
        let first = self.next()?;
        Some(self.fold(first, f))
    }

    // NOT SUPPORTED: Aeneas crashes on a where-clause fixing an associated type (`R: Try<Output = …>`),
    // aeneas#1493.
    /*
    fn try_reduce<R>(
        &mut self,
        f: impl [const] FnMut(Self::Item, Self::Item) -> R + [const] Destruct,
    ) -> ChangeOutputType<R, Option<R::Output>>
    where
        Self: Sized,
        R: [const] Try<Output = Self::Item, Residual: [const] Residual<Option<Self::Item>>>,
    {
        let first = match self.next() {
            Some(i) => i,
            None => return Try::from_output(None),
        };

        match self.try_fold(first, f).branch() {
            ControlFlow::Break(r) => FromResidual::from_residual(r),
            ControlFlow::Continue(i) => Try::from_output(Some(i)),
        }
    }
    */

    // NOT SUPPORTED: its body calls `try_fold`, which is commented out.
    /*
    fn all<F>(&mut self, f: F) -> bool
    where
        Self: Sized,
        F: [const] FnMut(Self::Item) -> bool + [const] Destruct,
    {
        #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
        #[inline]
        const fn check<T>(
            mut f: impl [const] FnMut(T) -> bool + [const] Destruct,
        ) -> impl [const] FnMut((), T) -> ControlFlow<()> + [const] Destruct {
            const move |(), x| {
                if f(x) { ControlFlow::Continue(()) } else { ControlFlow::Break(()) }
            }
        }
        self.try_fold((), check(f)) == ControlFlow::Continue(())
    }
    */

    // NOT SUPPORTED: its body calls `try_fold`, which is commented out.
    /*
    #[rustc_non_const_trait_method]
    fn any<F>(&mut self, f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        #[inline]
        fn check<T>(mut f: impl FnMut(T) -> bool) -> impl FnMut((), T) -> ControlFlow<()> {
            move |(), x| {
                if f(x) { ControlFlow::Break(()) } else { ControlFlow::Continue(()) }
            }
        }

        self.try_fold((), check(f)) == ControlFlow::Break(())
    }
    */

    // NOT SUPPORTED: its body calls `try_fold`, which is commented out.
    /*
    #[rustc_non_const_trait_method]
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        #[inline]
        fn check<T>(mut predicate: impl FnMut(&T) -> bool) -> impl FnMut((), T) -> ControlFlow<T> {
            move |(), x| {
                if predicate(&x) { ControlFlow::Break(x) } else { ControlFlow::Continue(()) }
            }
        }

        self.try_fold((), check(predicate)).break_value()
    }
    */

    // NOT SUPPORTED: its body calls `try_fold`, which is commented out.
    /*
    #[rustc_non_const_trait_method]
    fn find_map<B, F>(&mut self, f: F) -> Option<B>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> Option<B>,
    {
        #[inline]
        fn check<T, B>(mut f: impl FnMut(T) -> Option<B>) -> impl FnMut((), T) -> ControlFlow<B> {
            move |(), x| match f(x) {
                Some(x) => ControlFlow::Break(x),
                None => ControlFlow::Continue(()),
            }
        }

        self.try_fold((), check(f)).break_value()
    }
    */

    // NOT SUPPORTED: Aeneas crashes on a where-clause fixing an associated type (`R: Try<Output = …>`),
    // aeneas#1493.
    /*
    #[rustc_non_const_trait_method]
    fn try_find<R>(
        &mut self,
        f: impl FnMut(&Self::Item) -> R,
    ) -> ChangeOutputType<R, Option<Self::Item>>
    where
        Self: Sized,
        R: Try<Output = bool, Residual: Residual<Option<Self::Item>>>,
    {
        #[inline]
        fn check<I, V, R>(
            mut f: impl FnMut(&I) -> V,
        ) -> impl FnMut((), I) -> ControlFlow<R::TryType>
        where
            V: Try<Output = bool, Residual = R>,
            R: Residual<Option<I>>,
        {
            move |(), x| match f(&x).branch() {
                ControlFlow::Continue(false) => ControlFlow::Continue(()),
                ControlFlow::Continue(true) => ControlFlow::Break(Try::from_output(Some(x))),
                ControlFlow::Break(r) => ControlFlow::Break(FromResidual::from_residual(r)),
            }
        }

        match self.try_fold((), check(f)) {
            ControlFlow::Break(x) => x,
            ControlFlow::Continue(()) => Try::from_output(None),
        }
    }
    */

    // NOT SUPPORTED: its body calls `try_fold`, which is commented out.
    /*
    #[rustc_non_const_trait_method]
    fn position<P>(&mut self, predicate: P) -> Option<usize>
    where
        Self: Sized,
        P: FnMut(Self::Item) -> bool,
    {
        #[inline]
        fn check<'a, T>(
            mut predicate: impl FnMut(T) -> bool + 'a,
            acc: &'a mut usize,
        ) -> impl FnMut((), T) -> ControlFlow<usize, ()> + 'a {
            #[rustc_inherit_overflow_checks]
            move |_, x| {
                if predicate(x) {
                    ControlFlow::Break(*acc)
                } else {
                    *acc += 1;
                    ControlFlow::Continue(())
                }
            }
        }

        let mut acc = 0;
        self.try_fold((), check(predicate, &mut acc)).break_value()
    }
    */

    // NOT SUPPORTED: its body calls `try_rfold`, which is commented out.
    /*
    #[rustc_non_const_trait_method]
    fn rposition<P>(&mut self, predicate: P) -> Option<usize>
    where
        P: FnMut(Self::Item) -> bool,
        Self: Sized + ExactSizeIterator + DoubleEndedIterator,
    {
        // No need for an overflow check here, because `ExactSizeIterator`
        // implies that the number of elements fits into a `usize`.
        #[inline]
        fn check<T>(
            mut predicate: impl FnMut(T) -> bool,
        ) -> impl FnMut(usize, T) -> ControlFlow<usize, usize> {
            move |i, x| {
                let i = i - 1;
                if predicate(x) { ControlFlow::Break(i) } else { ControlFlow::Continue(i) }
            }
        }

        let n = self.len();
        self.try_rfold(n, check(predicate)).break_value()
    }
    */

    // NOT SUPPORTED: its body passes `Ord::max` as a closure, and Aeneas cannot translate the `FnMut` impl of
    // a trait method ("Unimplemented").
    /*
    fn max(self) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Ord + [const] Destruct,
    {
        self.reduce(Ord::max)
    }
    */

    // NOT SUPPORTED: its body passes `Ord::min` as a closure, and Aeneas cannot translate the `FnMut` impl of
    // a trait method ("Unimplemented").
    /*
    fn min(self) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Ord + [const] Destruct,
    {
        self.reduce(Ord::min)
    }
    */

    // NOT SUPPORTED: its body uses `map`, whose `Iterator` impl is then mutually recursive with this method,
    // aeneas#1264.
    /*
    #[rustc_non_const_trait_method]
    fn max_by_key<B: Ord, F>(self, f: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(&Self::Item) -> B,
    {
        // If we implemented this via `max_by` that would force it to use `B::cmp`.
        // By using `max` over `KeyAndValue`, it instead ends up calling `B::lt`
        // (via `KeyAndValue::max`), which is often overridden more efficiently.

        #[inline]
        fn key<T, B>(mut f: impl FnMut(&T) -> B) -> impl FnMut(T) -> KeyAndValue<B, T> {
            move |value| KeyAndValue { key: f(&value), value }
        }

        let KeyAndValue { value, .. } = self.map(key(f)).max()?;
        Some(value)
    }
    */

    // NOT SUPPORTED: its closure captures `&mut compare`, and Aeneas generates an ill-typed `call_mut` for it.
    /*
    fn max_by<F>(self, compare: F) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Destruct,
        F: [const] FnMut(&Self::Item, &Self::Item) -> Ordering + [const] Destruct,
    {
        #[inline]
        #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
        const fn fold<T>(
            mut compare: impl [const] FnMut(&T, &T) -> Ordering + [const] Destruct,
        ) -> impl [const] FnMut(T, T) -> T + [const] Destruct
        where
            T: [const] Destruct,
        {
            const move |x, y| cmp::max_by(x, y, &mut compare)
        }

        self.reduce(fold(compare))
    }
    */

    // NOT SUPPORTED: its body uses `map`, whose `Iterator` impl is then mutually recursive with this method,
    // aeneas#1264.
    /*
    #[rustc_non_const_trait_method]
    fn min_by_key<B: Ord, F>(self, f: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(&Self::Item) -> B,
    {
        // If we implemented this via `min_by` that would force it to use `B::cmp`.
        // By using `min` over `KeyAndValue`, it instead ends up calling `B::lt`
        // (via `KeyAndValue::min`), which is often overridden more efficiently.

        #[inline]
        fn key<T, B>(mut f: impl FnMut(&T) -> B) -> impl FnMut(T) -> KeyAndValue<B, T> {
            move |value| KeyAndValue { key: f(&value), value }
        }

        let KeyAndValue { value, .. } = self.map(key(f)).min()?;
        Some(value)
    }
    */

    // NOT SUPPORTED: its closure captures `&mut compare`, and Aeneas generates an ill-typed `call_mut` for it.
    /*
    fn min_by<F>(self, compare: F) -> Option<Self::Item>
    where
        Self: Sized + [const] Destruct,
        F: [const] FnMut(&Self::Item, &Self::Item) -> Ordering + [const] Destruct,
        Self::Item: [const] Destruct,
    {
        #[inline]
        #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
        const fn fold<T>(
            mut compare: impl [const] FnMut(&T, &T) -> Ordering + [const] Destruct,
        ) -> impl [const] FnMut(T, T) -> T + [const] Destruct
        where
            T: [const] Destruct,
        {
            const move |x, y| cmp::min_by(x, y, &mut compare)
        }

        self.reduce(fold(compare))
    }
    */

    fn rev(self) -> Rev<Self>
    where
        Self: Sized + DoubleEndedIterator,
    {
        Rev::new(self)
    }

    // NOT SUPPORTED: Aeneas crashes on a where-clause fixing an associated type
    // (`Self: Iterator<Item = …>`), aeneas#1493, #1491.
    /*
    #[rustc_non_const_trait_method]
    fn unzip<A, B, FromA, FromB>(self) -> (FromA, FromB)
    where
        FromA: Default + Extend<A>,
        FromB: Default + Extend<B>,
        Self: Sized + Iterator<Item = (A, B)>,
    {
        let mut unzipped: (FromA, FromB) = Default::default();
        unzipped.extend(self);
        unzipped
    }
    */

    // NOT SUPPORTED: Aeneas crashes on a where-clause fixing an associated type
    // (`Self: Iterator<Item = …>`), aeneas#1493, #1491.
    /*
    fn copied<'a, T>(self) -> Copied<Self>
    where
        T: Copy + 'a,
        Self: Sized + Iterator<Item = &'a T>,
    {
        Copied::new(self)
    }
    */

    // NOT SUPPORTED: Aeneas crashes on a where-clause fixing an associated type
    // (`Self: Iterator<Item = …>`), aeneas#1493, #1491.
    /*
    fn cloned<'a, T>(self) -> Cloned<Self>
    where
        T: Clone + 'a,
        Self: Sized + Iterator<Item = &'a T>,
    {
        Cloned::new(self)
    }
    */

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
        self.cmp_by(other, |x, y| x.cmp(&y))
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
        self.partial_cmp_by(other, |x, y| x.partial_cmp(&y))
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

    // NOT SUPPORTED: its body calls `eq_by`, which is commented out.
    /*
    #[rustc_non_const_trait_method]
    fn eq<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialEq<I::Item>,
        Self: Sized,
    {
        self.eq_by(other, |x, y| x == y)
    }
    */

    // NOT SUPPORTED: calls `SpecIterEq` (stubbed at the top of the file), whose two `Iterator` clauses both
    // become a Lean field named `IteratorInst`, aeneas#1051.
    /*
    #[rustc_non_const_trait_method]
    fn eq_by<I, F>(self, other: I, eq: F) -> bool
    where
        Self: Sized,
        I: IntoIterator,
        F: FnMut(Self::Item, I::Item) -> bool,
    {
        #[inline]
        fn compare<X, Y, F>(mut eq: F) -> impl FnMut(X, Y) -> ControlFlow<()>
        where
            F: FnMut(X, Y) -> bool,
        {
            move |x, y| {
                if eq(x, y) { ControlFlow::Continue(()) } else { ControlFlow::Break(()) }
            }
        }

        SpecIterEq::spec_iter_eq(self, other.into_iter(), compare(eq))
    }
    */

    // NOT SUPPORTED: its body calls `eq`, which is commented out.
    /*
    #[rustc_non_const_trait_method]
    fn ne<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialEq<I::Item>,
        Self: Sized,
    {
        !self.eq(other)
    }
    */

    #[rustc_non_const_trait_method]
    fn lt<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        self.partial_cmp(other) == Some(Ordering::Less)
    }

    #[rustc_non_const_trait_method]
    fn le<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        matches!(self.partial_cmp(other), Some(Ordering::Less | Ordering::Equal))
    }

    #[rustc_non_const_trait_method]
    fn gt<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        self.partial_cmp(other) == Some(Ordering::Greater)
    }

    #[rustc_non_const_trait_method]
    fn ge<I>(self, other: I) -> bool
    where
        I: IntoIterator,
        Self::Item: PartialOrd<I::Item>,
        Self: Sized,
    {
        matches!(self.partial_cmp(other), Some(Ordering::Greater | Ordering::Equal))
    }

    // NOT SUPPORTED: its body calls `is_sorted_by`, which is commented out.
    /*
    fn is_sorted(self) -> bool
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] PartialOrd + [const] Destruct,
    {
        self.is_sorted_by(const |a, b| a <= b)
    }
    */

    // NOT SUPPORTED: its body calls `all`, which is commented out.
    /*
    fn is_sorted_by<F>(mut self, compare: F) -> bool
    where
        Self: Sized + [const] Destruct,
        Self::Item: [const] Destruct,
        F: [const] FnMut(&Self::Item, &Self::Item) -> bool + [const] Destruct,
    {
        #[inline]
        #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
        const fn check<'a, T>(
            last: &'a mut T,
            mut compare: impl [const] FnMut(&T, &T) -> bool + 'a + [const] Destruct,
        ) -> impl [const] FnMut(T) -> bool + 'a + [const] Destruct
        where
            T: [const] Destruct,
        {
            const move |curr| {
                if !compare(last, &curr) {
                    return false;
                }
                *last = curr;
                true
            }
        }

        let mut last = match self.next() {
            Some(e) => e,
            None => return true,
        };

        self.all(check(&mut last, compare))
    }
    */

    // NOT SUPPORTED: its body uses `map`, whose `Iterator` impl is then mutually recursive with this method,
    // aeneas#1264.
    /*
    #[rustc_non_const_trait_method]
    fn is_sorted_by_key<F, K>(self, f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> K,
        K: PartialOrd,
    {
        self.map(f).is_sorted()
    }
    */

    #[doc(hidden)]
    unsafe fn __iterator_get_unchecked(&mut self, _idx: usize) -> Self::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // Always specialized
        unreachable!();
    }
}

// ---------------------------------------------------------------------------------------------
// `DoubleEndedIterator` (core/src/iter/traits/double_ended.rs)
// ---------------------------------------------------------------------------------------------

#[rustc_const_unstable(feature = "const_iter", issue = "92476")]
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

    // NOT SUPPORTED: `NonZero`'s trait `ZeroablePrimitive` gets two Lean fields named `markerCopyInst`.
    /*
    fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>>
    where
        Self::Item: [const] Destruct,
    {
        for i in 0..n {
            if self.next_back().is_none() {
                // SAFETY: `i` is always less than `n`.
                return Err(unsafe { NonZero::new_unchecked(n - i) });
            }
        }
        Ok(())
    }
    */

    // NOT SUPPORTED: its body calls `advance_back_by`, which is commented out.
    /*
    fn nth_back(&mut self, n: usize) -> Option<Self::Item>
    where
        Self::Item: [const] Destruct,
    {
        if self.advance_back_by(n).is_err() {
            return None;
        }
        self.next_back()
    }
    */

    // NOT SUPPORTED: Aeneas crashes on a where-clause fixing an associated type (`R: Try<Output = …>`),
    // aeneas#1493.
    /*
    fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: [const] FnMut(B, Self::Item) -> R + [const] Destruct,
        R: [const] Try<Output = B>,
    {
        let mut accum = init;
        while let Some(x) = self.next_back() {
            accum = f(accum, x)?;
        }
        try { accum }
    }
    */

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

    // NOT SUPPORTED: its body calls `try_rfold`, which is commented out.
    /*
    fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        Self: Sized,
        P: [const] FnMut(&Self::Item) -> bool + [const] Destruct,
        Self::Item: [const] Destruct,
    {
        #[inline]
        #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
        const fn check<T>(
            mut predicate: impl [const] FnMut(&T) -> bool + [const] Destruct,
        ) -> impl [const] FnMut((), T) -> ControlFlow<T> + [const] Destruct
        where
            T: [const] Destruct,
        {
            const move |(), x| {
                if predicate(&x) { ControlFlow::Break(x) } else { ControlFlow::Continue(()) }
            }
        }

        self.try_rfold((), check(predicate)).break_value()
    }
    */
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

#[rustc_const_unstable(feature = "const_iter", issue = "92476")]
pub const trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;
    fn into_iter(self) -> Self::IntoIter;
}

pub trait FromIterator<T>: Sized {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self;
}

#[rustc_const_unstable(feature = "const_iter", issue = "92476")]
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

// `Extend` for pairs, which `Iterator::unzip` uses (std implements it with a macro and private
// helpers, core/src/iter/traits/collect.rs).
impl<A, B, ExtendA: Extend<A>, ExtendB: Extend<B>> Extend<(A, B)> for (ExtendA, ExtendB) {
    fn extend<T: IntoIterator<Item = (A, B)>>(&mut self, into_iter: T) {
        let mut iter = into_iter.into_iter();
        while let Some((a, b)) = iter.next() {
            self.0.extend_one(a);
            self.1.extend_one(b);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// `Sum`, `Product` (core/src/iter/traits/accum.rs)
// ---------------------------------------------------------------------------------------------

#[rustc_const_unstable(feature = "const_iter", issue = "92476")]
pub const trait Sum<A = Self>: Sized {
    fn sum<I: Iterator<Item = A>>(iter: I) -> Self;
}

#[rustc_const_unstable(feature = "const_iter", issue = "92476")]
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

// Used only by `Iterator::try_collect`, which is commented out.
/*
/// The iterator `try_collect` collects from: the outputs, until the first residual.
pub struct GenericShunt<'a, I, R> {
    iter: I,
    residual: &'a mut Option<R>,
}
impl<'a, I: Iterator, R> Iterator for GenericShunt<'a, I, R>
where
    I::Item: Try<Residual = R>,
{
    type Item = <I::Item as Try>::Output;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            None => None,
            Some(x) => match x.branch() {
                ControlFlow::Continue(o) => Some(o),
                ControlFlow::Break(r) => {
                    *self.residual = Some(r);
                    None
                }
            },
        }
    }
}

/// Like `by_ref`, but requiring `Sized` (core/src/iter/adapters/by_ref_sized.rs).
pub struct ByRefSized<'a, I>(pub &'a mut I);
impl<I: Iterator> Iterator for ByRefSized<'_, I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<Self::Item> {
        I::next(self.0)
    }
}
*/

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
            // skips `step_minus_one` items (not with `nth`, which is commented out)
            let mut i = 0;
            while i < self.step_minus_one {
                let _ = self.iter.next();
                i += 1;
            }
            self.iter.next()
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
// NOT SUPPORTED: the closure takes `&mut St`, which `FnMut::call_mut` cannot hand back, aeneas#961,
// #1215. (`Iterator::scan` itself is fine.)
/*
impl<B, I: Iterator, St, F: FnMut(&mut St, I::Item) -> Option<B>> Iterator for Scan<I, St, F> {
    type Item = B;
    fn next(&mut self) -> Option<B> {
        match self.iter.next() {
            Some(a) => (self.f)(&mut self.state, a),
            None => None,
        }
    }
}
*/

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
// std's `new` (crate-private there), with the fields above.
impl<I> Copied<I> {
    pub(crate) const fn new(it: I) -> Copied<I> {
        Copied { it }
    }
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
// std's `new` (crate-private there), with the fields above.
impl<I> Cloned<I> {
    pub(crate) const fn new(it: I) -> Cloned<I> {
        Cloned { it }
    }
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
#[rustc_const_unstable(feature = "const_iter", issue = "92476")]
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
    // (not `collect`, which is commented out)
    <u32 as FromIterator<u32>>::from_iter(Count { n: 4 })
}
