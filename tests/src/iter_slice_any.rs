//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::test]
pub fn any_stops_after_match() {
    let bytes: [u8; 3] = [0, 1, 2];
    let mut iter = bytes.iter();
    assert!(iter.any(|byte| *byte != 0));
    assert!(*iter.next().unwrap() == 2);
    assert!(iter.next().is_none());
}

#[verify::test]
pub fn any_exhausts_without_match() {
    let bytes: [u8; 2] = [0, 0];
    let mut iter = bytes.iter();
    assert!(!iter.any(|byte| *byte != 0));
    assert!(iter.next().is_none());
}

#[verify::test]
pub fn any_threads_owned_predicate_state() {
    let bytes: [u8; 3] = [10, 20, 30];
    let mut calls = 0u8;
    let mut iter = bytes.iter();
    assert!(iter.any(move |_| {
        calls += 1;
        calls == 2
    }));
    assert!(*iter.next().unwrap() == 30);
}
