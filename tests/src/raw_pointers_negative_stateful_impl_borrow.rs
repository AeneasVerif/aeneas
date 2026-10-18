//@ [!lean] skip
//@ [lean] known-failure
//! Implementing a method of a trait declared in another crate by a method which
//! accesses the heap and returns a borrow is rejected: the model of the trait
//! method has a pure signature, which can not hold the backward function which
//! gives the value back to the heap.
use core::ptr::NonNull;

pub struct Ptr {
    pub p: NonNull<u32>,
}

impl AsRef<u32> for Ptr {
    fn as_ref(&self) -> &u32 {
        unsafe { self.p.as_ref() }
    }
}
