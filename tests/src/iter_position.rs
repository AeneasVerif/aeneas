//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::test]
pub fn position_found() {
    let xs = [4u32, 5, 6, 5];
    let target = 5u32;
    let at = match xs.iter().position(|x| *x == target) {
        Some(at) => at,
        None => 99,
    };
    assert!(at == 1);
}

#[verify::test]
pub fn position_missing() {
    let xs = [4u32, 5, 6];
    let target = 9u32;
    let at = match xs.iter().position(|x| x == &target) {
        Some(at) => at,
        None => 99,
    };
    assert!(at == 99);
}
