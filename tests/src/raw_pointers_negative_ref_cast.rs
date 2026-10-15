//@ [!lean] skip
//@ [lean] known-failure
//! Pointer casts of references are rejected (references are erased). The
//! interpreter rejects the raw pointers to types containing borrows first.

/// Reads the reference itself (its address) as an integer.
pub fn read_ref_as_u32(x: &u32) -> u32 {
    let p = &raw const x;
    unsafe { *(p as *const u32) }
}
