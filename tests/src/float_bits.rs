//@ [!lean] skip
//! Floats and unchecked strings, as used by ryu.

pub fn bits64(x: f64) -> u64 {
    x.to_bits()
}

pub fn bits32(x: f32) -> u32 {
    x.to_bits()
}

pub fn ascii(bytes: &[u8]) -> &str {
    unsafe { core::str::from_utf8_unchecked(bytes) }
}
