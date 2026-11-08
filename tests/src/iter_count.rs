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

/// `StepBy` uses the default `count`, which dispatches through `fold`.
#[verify::test]
pub fn count_step_by() {
    let values = [1u32, 2, 3, 4, 5];
    assert!(values.iter().step_by(2).count() == 3);
}
