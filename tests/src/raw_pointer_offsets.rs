//@ [!lean] skip
//! Distances between raw pointers derived from the same place.

unsafe fn write3(p: *mut u8) -> *mut u8 {
    *p = 1;
    *p.add(1) = 2;
    *p.add(2) = 3;
    p.add(3)
}

/// The two raw pointers to `buf` share the same allocation.
fn written_len(buf: &mut [u8; 8]) -> usize {
    let end = unsafe { write3(buf.as_mut_ptr()) };
    unsafe { end.offset_from(buf.as_ptr()) as usize }
}
