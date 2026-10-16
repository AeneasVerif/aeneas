//@ [!lean] skip
//@ [lean] known-failure
//! Raw borrows of fields of packed structs (which may be unaligned) are
//! rejected.

#[repr(C, packed)]
pub struct Packed {
    pub a: u8,
    pub b: u32,
}

pub fn read_packed_field(p: &Packed) -> u32 {
    let q = &raw const p.b;
    unsafe { q.read_unaligned() }
}
