//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `VecDeque::new`, `VecDeque::len`, `VecDeque::push_back`,
//! `VecDeque::pop_front`. Adapted from
//! <https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html>.

use std::collections::VecDeque;

#[verify::test]
pub fn test_vec_deque_push_pop() {
    // Adapted from the `push_back` and `pop_front` docs examples.
    let mut d: VecDeque<u32> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    assert!(d.len() == 3);
    let x = d.pop_front();
    match x {
        Some(v) => assert!(v == 1),
        None => panic!(),
    }
    assert!(d.len() == 2);
}

#[verify::test]
pub fn test_vec_deque_len_empty() {
    let d: VecDeque<u32> = VecDeque::new();
    assert!(d.len() == 0);
}
