//@ [!lean] skip
//! Pointer arithmetic backwards: `<*mut T>::sub` and `<*const T>::sub`.

pub unsafe fn write_back(end: *mut u8) -> u8 {
    *end.sub(1) = 2;
    *end.sub(2)
}

pub fn second_to_last(buf: &mut [u8; 4]) -> u8 {
    unsafe { write_back(buf.as_mut_ptr().add(4)) }
}

pub unsafe fn read_back(end: *const u32) -> u32 {
    *end.sub(1)
}
