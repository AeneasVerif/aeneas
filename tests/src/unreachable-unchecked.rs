//@ [!lean] skip
//! A call to `hint::unreachable_unchecked` at the end of a block (as in itoa's
//! `Buffer::format`): the call returns `!`, so nothing follows it in the block.
//! It is undefined behavior if reached.

pub fn check(x: u32) -> u32 {
    if x > 10 {
        unsafe { core::hint::unreachable_unchecked() }
    }
    x
}
