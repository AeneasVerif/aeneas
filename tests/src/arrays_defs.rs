//@ [!lean] skip

pub fn clone_array<T: Clone, const N: usize>(x: &[T; N]) -> [T; N] {
    x.clone()
}
