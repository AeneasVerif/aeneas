//@ [!lean] skip
//! A shared borrow obtained by dereferencing a raw pointer to a static, live
//! across a join (as in zmij's `write`): one of the joined contexts kept an
//! ignored value in the region abstraction of the dereference, and the contexts
//! could not be matched.
use std::ptr;
pub struct T {
    pub data: [u64; 4],
    pub x: u64,
}
pub static S: T = T {
    data: [1, 2, 3, 4],
    x: 7,
};
pub unsafe fn f(buffer: *mut u8, b: bool, i: usize) -> u64 {
    let d = ptr::addr_of!(S);
    let d = &*d;
    let mut e = *d.data.get_unchecked(i);
    e = e.to_le();
    ptr::copy_nonoverlapping(ptr::addr_of!(e).cast::<u8>(), buffer, if b { 5 } else { 4 });
    d.x
}
