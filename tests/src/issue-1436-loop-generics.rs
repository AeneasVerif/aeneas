//@ [!lean] skip
//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1436
//!
//! The functions introduced for loops are parameterized only by the generic
//! parameters used in the loop. When a trait clause is used in a loop, the
//! parameters appearing in that clause (e.g., the type `I` in the clause
//! `I: IntoIterator<Item = u32>`, translated to
//! `IntoIterator I u32 Clause0_IntoIter`) must be kept even if they are not
//! otherwise used in the loop.

/// `while let` loop over `I::IntoIter`: `I` only appears through the clause.
pub fn sum<I: IntoIterator<Item = u32>>(xs: I) -> u32 {
    let mut it = xs.into_iter();
    let mut acc = 0u32;
    while let Some(x) = it.next() {
        acc = acc.wrapping_add(x);
    }
    acc
}

/// `for` loop over an `impl IntoIterator` (the example from the issue).
pub fn rle(bytes: impl IntoIterator<Item = u8>) -> Vec<u8> {
    let mut v = Vec::new();
    let mut count = 1;
    let mut iter = bytes.into_iter();
    let Some(mut current) = iter.next() else {
        return v;
    };
    for next in iter {
        if next == current {
            if count == 255 {
                v.push(count);
                v.push(current);
                count = 1;
            } else {
                count += 1;
            }
        } else {
            v.push(count);
            v.push(current);
            count = 1;
            current = next;
        }
    }
    v.push(count);
    v.push(current);
    v
}

/// The item type is itself a generic parameter.
pub fn count<T, I: IntoIterator<Item = T>>(xs: I) -> u32 {
    let mut it = xs.into_iter();
    let mut n = 0u32;
    while let Some(_) = it.next() {
        n = n.wrapping_add(1);
    }
    n
}

pub trait Tr {
    fn f(&self) -> u32;
}

/// A trait whose only use is to provide its parent clause `Self: Tr`.
pub trait Wrap<T>: Tr {}

/// `T` only appears through the clause `W: Wrap<T>`, and this clause is only
/// used through its parent clause `W: Tr`.
pub fn loop_wrap<T, W: Wrap<T>>(w: &W, n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0;
    while i < n {
        acc = acc.wrapping_add(w.f());
        i += 1;
    }
    acc
}

pub trait HasN<const N: usize>: Tr {}

/// The const generic `N` only appears through the clause `X: HasN<N>`, and
/// this clause is only used through its parent clause `X: Tr`.
pub fn loop_const_generic<const N: usize, X: HasN<N>>(x: &X, n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0;
    while i < n {
        acc = acc.wrapping_add(x.f());
        i += 1;
    }
    acc
}

/// Same as [loop_wrap], but with nested parent clauses.
pub trait Wrap2<T>: Wrap<T> {}

pub fn loop_wrap2<T, W: Wrap2<T>>(w: &W, n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0;
    while i < n {
        acc = acc.wrapping_add(w.f());
        i += 1;
    }
    acc
}
