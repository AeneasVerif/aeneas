//@ [!lean] skip
//@ [lean] known-failure
//! Pointer casts which change the pointee type are accepted, unless one of the
//! types mentions `Box`, references or packed/aligned types: the translation
//! erases boxes and references (`Box<u32>`, `&u32` and `u32` are all `U32`).

/// Reads the box itself (its address) as an integer.
pub unsafe fn read_box_as_u32(p: *mut Box<u32>) -> u32 {
    *p.cast::<u32>()
}
