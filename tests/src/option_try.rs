//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the `?` operator on `Option`: `Some` continues, `None` returns early.

fn add_one(x: Option<u32>) -> Option<u32> {
    let v = x?;
    Some(v + 1)
}

fn first_two(v: &[u32]) -> Option<u32> {
    let a = v.get(0)?;
    let b = v.get(1)?;
    Some(*a + *b)
}

/// `Some` flows through `?`.
#[verify::test]
pub fn test_some_continues() {
    assert!(add_one(Some(41)).unwrap() == 42);
}

/// `None` returns early from the function.
#[verify::test]
pub fn test_none_returns_early() {
    assert!(add_one(None).is_none());
}

/// Several `?` in a row stop at the first `None`.
#[verify::test]
pub fn test_chained() {
    assert!(first_two(&[1, 2, 3]).unwrap() == 3);
    assert!(first_two(&[1]).is_none());
    assert!(first_two(&[]).is_none());
}
