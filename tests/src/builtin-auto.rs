//@ [!lean] skip
#![allow(unused)]
#![feature(ptr_metadata)]

use std::ptr::Pointee;

struct Inner {
    ptr: *const u8,
}

pub fn make() -> Box<Inner> {
    Box::new(Inner {
        ptr: std::ptr::null(),
    })
}

trait SuperPointee: Pointee {}

impl SuperPointee for u32 {}
