//@ [!lean] skip
//! `size_of::<T>()` for the types whose memory representation is their bytes.

pub fn sizes() -> usize {
    core::mem::size_of::<u64>() + core::mem::size_of::<u16>() + core::mem::size_of::<bool>()
}

#[test]
fn test_sizes() {
    assert_eq!(sizes(), 11);
}
