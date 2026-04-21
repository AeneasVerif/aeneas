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
