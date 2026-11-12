//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::test]
pub fn flatten_vecs() {
    let mut rows: Vec<Vec<u32>> = Vec::new();
    rows.push(vec![1, 2]);
    rows.push(Vec::new());
    rows.push(vec![3]);
    let flat: Vec<u32> = rows.into_iter().flatten().collect();
    assert!(flat.len() == 3);
    assert!(flat[0] == 1);
    assert!(flat[1] == 2);
    assert!(flat[2] == 3);
}

#[verify::test]
pub fn flatten_empty() {
    let rows: Vec<Vec<u32>> = Vec::new();
    let flat: Vec<u32> = rows.into_iter().flatten().collect();
    assert!(flat.len() == 0);
}
