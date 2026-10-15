//@ [!lean] skip
//@ [lean] known-failure
//! `write_bytes` on a box pointee is rejected (boxes are erased).

pub unsafe fn f(p: *mut Box<u32>) {
    p.write_bytes(0, 1)
}
