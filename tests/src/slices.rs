//@ [coq,fstar,borrow-check] skip

pub fn slice_subslice_from_shared(x: &[u32]) -> &[u32] {
    &x[0..]
}

pub fn slice_subslice_from_mut(x: &mut [u32]) -> &mut [u32] {
    &mut x[0..]
}
