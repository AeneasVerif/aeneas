//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub unsafe fn at(s: &[u32], i: usize) -> u32 {
    // The caller must ensure that i is in bounds.
    unsafe { *s.get_unchecked(i) }
}

pub unsafe fn range_len(s: &[u32], start: usize, end: usize) -> usize {
    // The caller must ensure start <= end <= s.len().
    unsafe { s.get_unchecked(start..end).len() }
}

#[verify::test]
pub fn regression() {
    let s = [10, 20];
    assert!(unsafe { at(&s, 0) } == 10);
    assert!(unsafe { at(&s, 1) } == 20);
    assert!(unsafe { range_len(&s, 0, 2) } == 2);
    assert!(unsafe { range_len(&s, 1, 2) } == 1);
    assert!(unsafe { range_len(&s, 2, 2) } == 0);
    assert!(unsafe { range_len(&[], 0, 0) } == 0);
}

#[cfg(test)]
#[test]
fn rust_regression() {
    regression();
}
