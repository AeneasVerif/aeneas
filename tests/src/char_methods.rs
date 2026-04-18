//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Test for `char` primitive: comparison.

fn make_a() -> char {
    'a'
}
fn make_b() -> char {
    'b'
}

#[verify::test]
pub fn test_char_eq() {
    let a: char = make_a();
    let b: char = make_b();
    assert!(a != b);
    assert!(a == a);
}
