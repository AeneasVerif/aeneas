//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub fn any_reports_nonzero() -> bool {
    let bytes: [u8; 3] = [0, 1, 2];
    bytes.iter().any(|byte| *byte != 0)
}

#[verify::test]
pub fn any_on_empty_slice() {
    let bytes: [u8; 0] = [];
    let mut iter = bytes.iter();
    assert!(!iter.any(|_| true));
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_nonzero() {
        assert!(any_reports_nonzero());
    }

    #[test]
    fn empty_slice() {
        any_on_empty_slice();
    }

    #[test]
    fn stops_after_match() {
        any_stops_after_match();
    }

    #[test]
    fn exhausts_without_match() {
        any_exhausts_without_match();
    }

    #[test]
    fn threads_owned_predicate_state() {
        any_threads_owned_predicate_state();
    }
}
