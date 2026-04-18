//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Test for `<[V]>::concat` where `V: Borrow<[T]>`. Adapted from the docs:
//! <https://doc.rust-lang.org/alloc/slice/trait.Concat.html>.

fn make_vecs() -> Vec<Vec<u32>> {
    let mut a: Vec<u32> = Vec::new();
    a.push(1);
    a.push(2);
    let mut b: Vec<u32> = Vec::new();
    b.push(3);
    let mut outer: Vec<Vec<u32>> = Vec::new();
    outer.push(a);
    outer.push(b);
    outer
}

#[verify::test]
pub fn test_concat() {
    let v = make_vecs();
    let flat: Vec<u32> = v.concat();
    assert!(flat.len() == 3);
}
