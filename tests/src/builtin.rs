//@ charon-args=--exclude=core::fmt::Debug::fmt --opaque=core::fmt::Formatter
//@[!lean] skip
//! This file uses a list of builtin definitions, to make sure they are properly
//! detected and mapped to definitions in the standard library.

fn clone_bool(x: bool) -> bool {
    x.clone()
}

fn clone_u32(x: u32) -> u32 {
    x.clone()
}

fn into_from<T, U: From<T>>(x: T) -> U {
    x.into()
}

fn into_same<T>(x: T) -> T {
    x.into()
}

fn from_same<T>(x: T) -> T {
    T::from(x)
}

fn copy<T: Copy>(x: &T) -> T {
    *x
}

fn u32_from_le_bytes(x: [u8; 4]) -> u32 {
    u32::from_le_bytes(x)
}

fn u32_to_le_bytes(x: u32) -> [u8; 4] {
    x.to_le_bytes()
}

fn use_debug_clause<T: core::fmt::Debug>(_: T) {}
