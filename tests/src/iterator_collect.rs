//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `Iterator::collect` + `Iterator::map` over ranges, slices, vecs.

fn make_range() -> core::ops::Range<usize> {
    0..3
}

#[verify::test]
pub fn test_range_collect_vec() {
    // Adapted from the `collect` docs:
    // let doubled: Vec<i32> = (1..=5).map(|i| i * 2).collect();
    let r = make_range();
    let v: Vec<usize> = r.collect();
    assert!(v.len() == 3);
}
