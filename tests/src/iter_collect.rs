//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::test]
pub fn collect_vec_from_slice() {
    let xs = [3u32, 1, 2];
    let ys: Vec<&u32> = xs.iter().collect();
    assert!(ys.len() == 3);
    assert!(*ys[0] == 3);
}

#[verify::test]
pub fn collect_vec_rev() {
    let xs = [3u32, 1, 2];
    let ys: Vec<&u32> = xs.iter().rev().collect();
    assert!(ys.len() == 3);
    assert!(*ys[0] == 2);
    assert!(*ys[2] == 3);
}
