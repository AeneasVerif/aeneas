//@ [!lean] skip

pub fn slice_subslice_from_shared(x: &[u32]) -> &[u32] {
    &x[0..]
}

pub fn slice_subslice_from_mut(x: &mut [u32]) -> &mut [u32] {
    &mut x[0..]
}

pub fn split_at<T>(x: &[T], n: usize) -> (&[T], &[T]) {
    x.split_at(n)
}

pub fn split_at_mut<T>(x: &mut [T], n: usize) -> (&mut [T], &mut [T]) {
    x.split_at_mut(n)
}

pub fn swap<T>(x: &mut [T], n: usize, m: usize) {
    x.swap(n, m)
}

pub fn from_vec<T>(x: Vec<T>) -> Box<[T]> {
    From::from(x)
}
