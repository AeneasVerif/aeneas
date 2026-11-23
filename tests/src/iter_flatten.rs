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
pub fn flatten_fold() {
    let mut rows: Vec<Vec<u32>> = Vec::new();
    rows.push(vec![1, 2]);
    rows.push(vec![3]);
    let sum = rows.into_iter().flatten().fold(0u32, |acc, x| acc * 10 + x);
    assert!(sum == 123);
}

#[verify::test]
pub fn vec_into_iter_fold() {
    let mut xs: Vec<u32> = Vec::new();
    xs.push(4);
    xs.push(5);
    let sum = xs.into_iter().fold(0u32, |acc, x| acc * 10 + x);
    assert!(sum == 45);
}

#[verify::test]
pub fn flatten_empty() {
    let rows: Vec<Vec<u32>> = Vec::new();
    let flat: Vec<u32> = rows.into_iter().flatten().collect();
    assert!(flat.len() == 0);
}
