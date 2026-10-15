//@ [!lean] skip
//@ [lean] known-failure
//! `PackedWord` is an alias of `U32` with alignment 4 in the model, while its
//! Rust alignment is 1: casting pointers to it is rejected.

#[repr(packed)]
pub struct PackedWord(u32);

pub fn f(x: &[PackedWord; 2]) -> u32 {
    unsafe { (&raw const *x).cast::<u32>().add(1).read_unaligned() }
}
