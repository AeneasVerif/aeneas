//@ [!lean] skip

fn bytes_of_words(data: &[u32]) -> *const u8 {
    data.as_ptr() as *const u8
}

fn mut_bytes_of_words(data: &mut [u32]) -> *mut u8 {
    data.as_mut_ptr() as *mut u8
}

fn const_bytes_of_mut_words(data: &mut [u32]) -> *const u8 {
    data.as_mut_ptr() as *const u8
}

fn signed_of_unsigned(data: &mut [u16]) -> *mut i16 {
    data.as_mut_ptr() as *mut i16
}

fn words_of_bytes(data: &[u8]) -> *const u32 {
    data.as_ptr() as *const u32
}
