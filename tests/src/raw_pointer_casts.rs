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

fn write_read_unaligned(buf: &mut [u8; 3], v: u16) -> u16 {
    let p = buf.as_mut_ptr();
    unsafe {
        let q = p.add(1).cast::<u16>();
        q.write_unaligned(v);
        q.read_unaligned()
    }
}

fn words_of_bytes_method(data: &[u8]) -> *const u32 {
    data.as_ptr().cast::<u32>()
}

fn word_of_array(p: *const [u8; 4]) -> *const u32 {
    p as *const u32
}
