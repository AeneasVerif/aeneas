//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::test]
pub fn map_or_some() {
    let x = Some(3u32);
    assert!(x.map_or(0, |v| v + 1) == 4);
}

#[verify::test]
pub fn map_or_none() {
    let x: Option<u32> = None;
    assert!(x.map_or(7, |v| v + 1) == 7);
}

#[verify::test]
pub fn option_into_iter_some() {
    let mut it = Some(5u32).into_iter();
    let first = match it.next() {
        Some(v) => v,
        None => 0,
    };
    assert!(first == 5);
    let second = match it.next() {
        Some(v) => v,
        None => 0,
    };
    assert!(second == 0);
}

fn nothing() -> Option<u32> {
    None
}

#[verify::test]
pub fn option_into_iter_none() {
    let mut it = nothing().into_iter();
    let first = match it.next() {
        Some(v) => v,
        None => 9,
    };
    assert!(first == 9);
}

#[verify::test]
pub fn vec_remove() {
    let mut v: Vec<u32> = Vec::new();
    v.push(10);
    v.push(20);
    v.push(30);
    let gone = v.remove(1);
    assert!(gone == 20);
    assert!(v.len() == 2);
    assert!(v[0] == 10);
    assert!(v[1] == 30);
}

fn same<T: PartialEq>(a: &T, b: &T) -> bool {
    a == b
}

#[verify::test]
pub fn char_eq() {
    assert!(same(&'a', &'a'));
    assert!(!same(&'a', &'b'));
}
