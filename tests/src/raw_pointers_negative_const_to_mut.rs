//@ [!lean] skip
//@ [lean] known-failure
//! Casting a `*const T` into a `*mut U` is rejected.

pub unsafe fn f(p: *const u32) -> *mut u8 {
    p as *mut u8
}
