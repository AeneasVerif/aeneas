//@ [!lean] skip
//! Test: const generic parameter shadowed by associated constant with the same name.
//!
//! When a trait has a const generic parameter `N` and also declares an associated
//! constant `N`, the extracted Lean structure must emit the associated constant
//! *after* the method signatures. Otherwise, the field `N` shadows the const
//! generic parameter `N` in the method types, causing elaboration failures (#usize).

/// A trait with a const generic `N` and an associated constant also called `N`.
/// The method `get` uses the const generic `N` in its signature (via `[u8; N]`).
trait HasConst<const N: usize> {
    const N: usize;

    fn get(&self) -> [u8; N];
}

/// A concrete implementation for testing.
struct Foo;

impl HasConst<4> for Foo {
    const N: usize = 42;

    fn get(&self) -> [u8; 4] {
        [0; 4]
    }
}

/// A function that uses the trait, exercising both the const generic and the
/// associated constant.
fn use_has_const<const N: usize, T: HasConst<N>>(x: &T) -> ([u8; N], usize) {
    let arr = x.get();
    let n = T::N;
    (arr, n)
}
