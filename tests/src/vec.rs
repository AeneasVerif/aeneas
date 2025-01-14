//@ [coq,fstar,borrow-check] skip

use std::vec::Vec;

fn use_extend_from_slice<T: Clone>(v: &mut Vec<T>, s: &[T]) {
    v.extend_from_slice(s)
}

fn use_alloc_with_capacity<T>(n: usize) -> Vec<T> {
    Vec::with_capacity(n)
}
