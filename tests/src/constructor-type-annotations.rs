//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

// ---------------------------------------------------------------------------
// constructors whose type parameters are not all used by their fields: the
// translation must annotate them, otherwise Lean cannot infer those parameters
// ---------------------------------------------------------------------------

/// None uses no type parameter
#[verify::test]
pub fn test_none() {
    let x: Option<u32> = None;
    assert!(x.is_none());
}

/// Ok does not use the error type
#[verify::test]
pub fn test_ok() {
    let r: Result<u32, u32> = Ok(2);
    assert!(r.is_ok());
}

/// Err does not use the success type
#[verify::test]
pub fn test_err() {
    let r: Result<u32, u32> = Err(3);
    assert!(!r.is_ok());
}

/// None determines nothing, so the outer Some is annotated, which also gives the inner None its type
#[verify::test]
pub fn test_some_none() {
    let x: Option<Option<u32>> = Some(None);
    assert!(x.is_some());
}

pub enum Slot<T> {
    Empty,
    Full(T),
}

pub fn slot_is_empty<T>(s: Slot<T>) -> bool {
    match s {
        Slot::Empty => true,
        Slot::Full(_) => false,
    }
}

/// the same for a user-defined enum: Empty uses no type parameter
#[verify::test]
pub fn test_slot_empty() {
    let s: Slot<u32> = Slot::Empty;
    assert!(slot_is_empty(s));
}

// ---------------------------------------------------------------------------
// the same inside a tuple and a structure (shapes from the tests of #1021):
// they are only as inferable as their fields
// ---------------------------------------------------------------------------

pub fn snd_is_none<T>(p: (bool, Option<T>)) -> bool {
    p.1.is_none()
}

#[verify::test]
pub fn test_tuple_none() {
    let p: (bool, Option<u32>) = (true, None);
    assert!(snd_is_none(p));
}

pub struct Holder<T> {
    pub value: Option<T>,
}

pub fn holder_is_none<T>(h: Holder<T>) -> bool {
    h.value.is_none()
}

#[verify::test]
pub fn test_struct_none() {
    let h: Holder<u32> = Holder { value: None };
    assert!(holder_is_none(h));
}
