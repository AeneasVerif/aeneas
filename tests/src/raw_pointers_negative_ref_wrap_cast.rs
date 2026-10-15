//@ [!lean] skip
//@ [lean] known-failure
//! `RefWrap` is translated to an alias of `U64`: casting pointers to it is
//! rejected. The interpreter rejects the raw pointers to types containing
//! borrows first.

pub struct RefWrap<'a>(&'a u64);

pub fn f(x: RefWrap) -> u64 {
    let p = &raw const x;
    unsafe { *(p as *const u64) }
}
