//@ [!lean] skip
//@ [lean] known-failure
//! Pointer casts which change the pointee type are rejected (other than the
//! casts adding or removing one `MaybeUninit`): several Rust types have the
//! same Lean type, so the typed heap model can not distinguish them.

/// Reads the box itself (its address) as an integer.
pub unsafe fn read_box_as_u32(p: *mut Box<u32>) -> u32 {
    *p.cast::<u32>()
}

/// Reads the reference itself (its address) as an integer.
pub unsafe fn read_ref_as_u32(p: *const &u32) -> u32 {
    *(p as *const u32)
}
