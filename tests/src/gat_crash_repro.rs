//! Minimal reproduction of issue #1195: aeneas hard crash related to certain GATs.
//!
//! This test case isolates the simplest pattern that triggers the crash so
//! maintainers can reproduce and fix the underlying cause without needing
//! the full original codebase.

/// A GAT (generic associated type) with a lifetime parameter.
pub trait Container {
    type Item<'a>
    where
        Self: 'a;

    fn get<'a>(&'a self) -> Self::Item<'a>;
}

/// Simple concrete implementation using a reference.
pub struct Wrapper<T>(T);

impl<T> Container for Wrapper<T> {
    type Item<'a> = &'a T where Self: 'a;

    fn get<'a>(&'a self) -> &'a T {
        &self.0
    }
}

/// Using the GAT through a generic bound — this pattern triggers the crash.
pub fn use_container<C: Container>(c: &C) -> C::Item<'_> {
    c.get()
}

pub fn main() {
    let w = Wrapper(42u32);
    let _val = use_container(&w);
}
