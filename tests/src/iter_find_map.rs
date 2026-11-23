//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::test]
pub fn find_map_found() {
    let xs = [1u32, 2, 3, 4];
    let found = match xs
        .iter()
        .find_map(|x| if *x > 2 { Some(*x * 10) } else { None })
    {
        Some(found) => found,
        None => 0,
    };
    assert!(found == 30);
}

#[verify::test]
pub fn find_map_missing() {
    let xs = [1u32, 2];
    let found = match xs.iter().find_map(|x| if *x > 2 { Some(*x) } else { None }) {
        Some(found) => found,
        None => 0,
    };
    assert!(found == 0);
}

/// `rev` on a slice iterator, and a closure that captures a reference and searches another slice.
#[verify::test]
pub fn find_map_rev_captured() {
    let xs = [1u32, 2, 3, 4];
    let pool = [2u32, 3];
    let found = match xs
        .iter()
        .rev()
        .find_map(|x| pool.iter().position(|p| p == x))
    {
        Some(found) => found,
        None => 99,
    };
    assert!(found == 1);
}
