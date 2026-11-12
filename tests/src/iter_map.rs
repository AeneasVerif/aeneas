//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::test]
pub fn map_slice() {
    let xs = [1u32, 2, 3];
    let offset = 10u32;
    let ys: Vec<u32> = xs.iter().map(|x| *x + offset).collect();
    assert!(ys.len() == 3);
    assert!(ys[0] == 11);
    assert!(ys[2] == 13);
}

#[verify::test]
pub fn map_stateful_closure() {
    let xs = [1u32, 2, 3];
    let mut seen = 0u32;
    let ys: Vec<u32> = xs
        .iter()
        .map(move |x| {
            seen += 1;
            *x * seen
        })
        .collect();
    assert!(ys[0] == 1);
    assert!(ys[1] == 4);
    assert!(ys[2] == 9);
}

pub fn map_generic<I: Iterator<Item = u32>>(it: I) -> Vec<u32> {
    it.map(|x| x + 1).collect()
}
