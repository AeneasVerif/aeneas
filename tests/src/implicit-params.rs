//@ [!lean] skip

use std::marker::PhantomData;

/// An enum where one type parameter (A) only appears in a trait bound,
/// making it implicit in the extracted Lean code. The trait clause
/// parameter must appear (not A) in the constructor return type.
pub enum Holder<K, A: Clone> {
    Value(K),
    Phantom(PhantomData<A>),
}

pub fn make_value<K, A: Clone>(k: K) -> Holder<K, A> {
    Holder::Value(k)
}
