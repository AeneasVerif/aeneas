//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! The built-in `Clone` impls of tuples.

pub fn clone_unit(x: &()) -> () {
    x.clone()
}

pub fn clone_tuple1(x: &(u32,)) -> (u32,) {
    x.clone()
}

pub fn clone_tuple2(x: &(u32, bool)) -> (u32, bool) {
    x.clone()
}

pub fn clone_tuple3(x: &(u32, bool, u8)) -> (u32, bool, u8) {
    x.clone()
}

pub fn clone_tuple4(x: &(u32, bool, u8, u64)) -> (u32, bool, u8, u64) {
    x.clone()
}

pub fn clone_tuple5(x: &(u32, bool, u8, u64, i32)) -> (u32, bool, u8, u64, i32) {
    x.clone()
}

pub fn clone_tuple6(x: &(u32, bool, u8, u64, i32, u16)) -> (u32, bool, u8, u64, i32, u16) {
    x.clone()
}

pub fn clone_nested(x: &((u32, bool), (), u8)) -> ((u32, bool), (), u8) {
    x.clone()
}

/// Clone through a generic `T: Clone`, so that the impl is used as a trait instance.
pub fn clone_generic<T: Clone>(x: &T) -> T {
    x.clone()
}

pub fn clone_generic_tuples(
    x: &(u32, bool),
    y: &(u32, bool, u8),
) -> ((u32, bool), (u32, bool, u8)) {
    (clone_generic(x), clone_generic(y))
}

/// Clone a tuple of generic, non-`Copy` elements.
pub fn clone_tuple_generic<A: Clone, B: Clone>(x: &(A, B)) -> (A, B) {
    x.clone()
}

/// Use `clone_from`.
pub fn clone_from_tuple(x: &mut (u32, bool), y: &(u32, bool)) {
    x.clone_from(y)
}

// Note: we compare the fields one by one because tuple `==` is not modelled.
#[verify::test]
pub fn test_clone_tuples() {
    clone_unit(&());
    let x = clone_tuple1(&(1,));
    assert!(x.0 == 1);
    let x = clone_tuple2(&(1, true));
    assert!(x.0 == 1 && x.1);
    let x = clone_tuple3(&(1, true, 2));
    assert!(x.0 == 1 && x.1 && x.2 == 2);
    let x = clone_tuple4(&(1, true, 2, 3));
    assert!(x.0 == 1 && x.1 && x.2 == 2 && x.3 == 3);
    let x = clone_tuple5(&(1, true, 2, 3, -4));
    assert!(x.0 == 1 && x.1 && x.2 == 2 && x.3 == 3 && x.4 == -4);
    let x = clone_tuple6(&(1, true, 2, 3, -4, 5));
    assert!(x.0 == 1 && x.1 && x.2 == 2 && x.3 == 3 && x.4 == -4 && x.5 == 5);
    let x = clone_nested(&((1, true), (), 2));
    assert!(x.0 .0 == 1 && x.0 .1 && x.2 == 2);
    let (x, y) = clone_generic_tuples(&(1, true), &(3, false, 2));
    assert!(x.0 == 1 && x.1 && y.0 == 3 && !y.1 && y.2 == 2);
    let x = clone_tuple_generic(&(1u32, false));
    assert!(x.0 == 1 && !x.1);
    let mut x = (0, false);
    clone_from_tuple(&mut x, &(1, true));
    assert!(x.0 == 1 && x.1);
}

#[cfg(test)]
mod tests {
    #[test]
    fn clone_tuples() {
        super::test_clone_tuples()
    }
}
