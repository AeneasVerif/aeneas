//@ [!lean] skip
//! Implementing a method of a trait declared in the crate by a method which
//! accesses the heap and returns a borrow: the method is stateful in the trait
//! declaration too, which holds the backward function giving the value back to
//! the heap. (For a trait declared in another crate, see
//! raw_pointers_negative_stateful_impl_borrow.rs.)
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
