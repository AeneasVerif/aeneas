//@ [!lean] skip

use std::cmp::Ordering;

pub fn compare<T: Ord>(x: &T, y: &T) -> Ordering {
    x.cmp(y)
}

pub fn u32_compare(x: u32, y: u32) -> Ordering {
    x.cmp(&y)
}

pub fn u64_partial_cmp(x: u64, y: u64) -> Option<Ordering> {
    x.partial_cmp(&y)
}

/// Exercises derived PartialOrd and Ord on a struct with scalar fields.
/// The derived impls only generate partial_cmp/cmp — the remaining methods
/// (lt, le, gt, ge, max, min, clamp) use defaults. The Lean structure
/// definitions must provide default field values for these.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Wrap(u64);

pub fn wrap_partial_cmp(x: &Wrap, y: &Wrap) -> Option<Ordering> {
    x.partial_cmp(y)
}

pub fn wrap_cmp(x: &Wrap, y: &Wrap) -> Ordering {
    x.cmp(y)
}
