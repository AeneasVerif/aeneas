//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
use std::marker::PhantomData;

// ---------------------------------------------------------------------------
// a tuple struct is extracted as a type definition (unit, its field, or the
// product of its fields), which drops the parameters its fields don't use: an
// argument of this type can't determine them, so they must be explicit
// ---------------------------------------------------------------------------

/// no fields: extracted as unit
pub struct Wrap<const N: usize>;

pub fn use_wrap<const N: usize>(_w: &Wrap<N>) -> bool {
    true
}

#[verify::test]
pub fn test_unit_struct() {
    let w: Wrap<4> = Wrap;
    assert!(use_wrap(&w));
}

/// one field which doesn't use the parameter: extracted as u32
pub struct Len<const N: usize>(u32);

pub fn len_value<const N: usize>(l: Len<N>) -> u32 {
    l.0
}

#[verify::test]
pub fn test_one_field() {
    let l: Len<3> = Len(5);
    assert!(len_value(l) == 5);
}

/// several fields, the parameter appearing only in a nested unit struct
/// (PhantomData is one as well)
pub struct Tagged<T>(u32, PhantomData<T>);

pub fn tagged_value<T>(t: Tagged<T>) -> u32 {
    t.0
}

#[verify::test]
pub fn test_nested() {
    let t: Tagged<bool> = Tagged(7, PhantomData);
    assert!(tagged_value(t) == 7);
}

/// the parameter appears in a field: it stays implicit
pub struct Pair<T>(T, u32);

pub fn pair_snd<T>(p: Pair<T>) -> u32 {
    p.1
}

#[verify::test]
pub fn test_used_param() {
    let p: Pair<bool> = Pair(true, 2);
    assert!(pair_snd(p) == 2);
}

/// the parameter is determined by another input: it stays implicit
pub fn wrap_len<const N: usize>(_w: &Wrap<N>, a: [u8; N]) -> usize {
    a.len()
}

#[verify::test]
pub fn test_other_input() {
    let w: Wrap<2> = Wrap;
    assert!(wrap_len(&w, [0, 1]) == 2);
}

/// the function introduced for the loop takes the tuple struct as well
pub fn loop_wrap<const N: usize>(w: Wrap<N>, n: u32) -> Wrap<N> {
    let mut w = w;
    let mut i = 0;
    while i < n {
        w = Wrap;
        i += 1;
    }
    w
}

#[verify::test]
pub fn test_loop() {
    let w: Wrap<4> = loop_wrap(Wrap, 3);
    assert!(use_wrap(&w));
}
