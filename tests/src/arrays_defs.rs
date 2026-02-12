//@ [!lean] skip

pub fn clone_array<T: Clone, const N: usize>(x: &[T; N]) -> [T; N] {
    x.clone()
}

pub fn index_slice_0<T>(s: &[T]) -> &T {
    &s[0]
}

pub fn index_empty_array() {
    let _ = index_slice_0::<u32>(&[]);
}
