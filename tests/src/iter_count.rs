//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods
#![feature(register_tool)]
#![register_tool(verify)]

/// Slice iterators override `count` with their remaining length.
#[verify::test]
pub fn count_slice() {
    let values = [1u32, 2, 3];
    assert!(values.iter().count() == 3);
}

#[verify::test]
pub fn count_empty_slice() {
    let values: [u32; 0] = [];
    assert!(values.iter().count() == 0);
}

#[verify::test]
pub fn count_slice_through_generic() {
    let values = [1u32, 2, 3];
    assert!(count_generic(values.iter()) == 3);
}

struct OneShot {
    value: Option<u32>,
}

impl Iterator for OneShot {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.value;
        self.value = None;
        value
    }
}

/// The default `count` is available through a generic iterator instance.
#[verify::test]
pub fn count_default_through_generic() {
    assert!(count_generic(OneShot { value: Some(9) }) == 1);
}

struct EmptyWithCountOverride;

impl Iterator for EmptyWithCountOverride {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }

    fn count(self) -> usize {
        7
    }
}

fn count_generic<I: Iterator>(iter: I) -> usize {
    iter.count()
}

#[verify::test]
pub fn count_override_through_generic() {
    assert!(count_generic(EmptyWithCountOverride) == 7);
}

struct FoldOnly;

impl Iterator for FoldOnly {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        f(init, 5)
    }
}

// The deliberately different `next` and `fold` results make dispatch observable.
#[verify::test]
pub fn count_dispatches_to_fold_override() {
    assert!(count_generic(FoldOnly) == 1);
}
