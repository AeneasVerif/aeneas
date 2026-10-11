//@ [!lean] skip
//@ [lean] known-failure
//! Implementing a trait method by a method which accesses the heap and returns
//! a borrow is rejected: the model of the trait method has a pure signature,
//! which can not hold the backward function which gives the value back to the
//! heap.
use core::ptr::NonNull;

pub trait Get {
    fn get(&self) -> &u32;
}

pub struct Ptr {
    pub p: NonNull<u32>,
}

impl Get for Ptr {
    fn get(&self) -> &u32 {
        unsafe { self.p.as_ref() }
    }
}
