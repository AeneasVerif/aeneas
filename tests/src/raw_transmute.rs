//@ [!lean] skip
//@ [lean] skip
// Lean models are handwritten until compiler transmute wiring is supported.

/// # Safety
/// `words` must point to an initialized, writable u32.
pub unsafe fn u32_round_trip(words: *mut u32, value: u32) -> u32 {
    let bytes: *mut u8 = std::mem::transmute(words);
    let words_again: *mut u32 = std::mem::transmute(bytes);
    words_again.write(value);
    words_again.read()
}

/// # Safety
/// `words` must point to an initialized, writable u32.
pub unsafe fn u8_round_trip(words: *mut u32, value: u8) -> u8 {
    let bytes: *mut u8 = std::mem::transmute(words);
    bytes.write(value);
    bytes.read()
}

/// # Safety
/// `words` must point to an initialized, writable u32.
pub unsafe fn word_to_byte(words: *mut u32, value: u32) -> u8 {
    words.write(value);
    let bytes: *mut u8 = std::mem::transmute(words);
    bytes.read()
}

/// # Safety
/// `words` must point to an initialized, writable u32.
pub unsafe fn byte_to_word(words: *mut u32, value: u8) -> u32 {
    let bytes: *mut u8 = std::mem::transmute(words);
    bytes.write(value);
    words.read()
}

#[test]
fn array_views() {
    let mut words = [7u32, 8u32];
    unsafe {
        let second = words.as_mut_ptr().add(1);
        assert_eq!(u32_round_trip(second, 0x01020304), 0x01020304);
        assert_eq!(u8_round_trip(second, 23), 23);
        let byte = word_to_byte(second, 0x01020304);
        assert_eq!(u8_round_trip(second, byte), byte);
        let word = byte_to_word(second, 42);
        assert_eq!(u32_round_trip(second, word), word);
    }
    assert_eq!(words[0], 7);
}
