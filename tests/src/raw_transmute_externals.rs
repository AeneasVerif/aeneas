//@ [!lean] skip
//@ charon-args=--opaque=crate::ext
//@ [lean] subdir=RawTransmuteExternals
//@ [lean] aeneas-args=-split-files -all-computable

// Keep the pointer operations opaque so the existing compiler emits ordinary
// calls. Their transparent Lean models live in FunsExternal.lean.
pub mod ext {
    /// # Safety
    /// Casting does not authorize dereferencing the resulting pointer.
    pub unsafe fn transmute_mut<T, U>(p: *mut T) -> *mut U {
        std::mem::transmute(p)
    }

    /// # Safety
    /// Casting does not authorize dereferencing the resulting pointer.
    pub unsafe fn transmute_const<T, U>(p: *const T) -> *const U {
        std::mem::transmute(p)
    }

    /// # Safety
    /// `p` must point to a readable, initialized u32.
    pub unsafe fn read_word(p: *mut u32) -> u32 {
        p.read()
    }

    /// # Safety
    /// `p` must point to a writable u32.
    pub unsafe fn write_word(p: *mut u32, value: u32) {
        p.write(value);
    }

    /// # Safety
    /// `p` must point to a readable, initialized byte.
    pub unsafe fn read_byte(p: *mut u8) -> u8 {
        p.read()
    }

    /// # Safety
    /// `p` must point to a writable byte.
    pub unsafe fn write_byte(p: *mut u8, value: u8) {
        p.write(value);
    }
}

pub unsafe fn mut_pointer_round_trip(words: *mut u32) -> *mut u32 {
    let bytes = ext::transmute_mut::<u32, u8>(words);
    ext::transmute_mut::<u8, u32>(bytes)
}

pub unsafe fn const_pointer_round_trip(words: *const u32) -> *const u32 {
    let bytes = ext::transmute_const::<u32, u8>(words);
    ext::transmute_const::<u8, u32>(bytes)
}

/// # Safety
/// `words` must point to an initialized, writable u32.
pub unsafe fn u32_round_trip(words: *mut u32, value: u32) -> u32 {
    let bytes = ext::transmute_mut::<u32, u8>(words);
    let words_again = ext::transmute_mut::<u8, u32>(bytes);
    ext::write_word(words_again, value);
    ext::read_word(words_again)
}

/// # Safety
/// `words` must point to an initialized, writable u32.
pub unsafe fn u8_round_trip(words: *mut u32, value: u8) -> u8 {
    let bytes = ext::transmute_mut::<u32, u8>(words);
    ext::write_byte(bytes, value);
    ext::read_byte(bytes)
}

/// # Safety
/// `words` must point to an initialized, writable u32.
pub unsafe fn word_to_byte(words: *mut u32, value: u32) -> u8 {
    ext::write_word(words, value);
    let bytes = ext::transmute_mut::<u32, u8>(words);
    ext::read_byte(bytes)
}

/// # Safety
/// `words` must point to an initialized, writable u32.
pub unsafe fn byte_to_word(words: *mut u32, value: u8) -> u32 {
    let bytes = ext::transmute_mut::<u32, u8>(words);
    ext::write_byte(bytes, value);
    ext::read_word(words)
}

#[test]
fn array_views() {
    let mut words = [7u32, 8u32];
    unsafe {
        let shared = words.as_ptr().add(1);
        assert_eq!(const_pointer_round_trip(shared), shared);
        let second = words.as_mut_ptr().add(1);
        assert_eq!(mut_pointer_round_trip(second), second);
        assert_eq!(u32_round_trip(second, 0x01020304), 0x01020304);
        assert_eq!(u8_round_trip(second, 23), 23);
        let byte = word_to_byte(second, 0x01020304);
        assert_eq!(u8_round_trip(second, byte), byte);
        let word = byte_to_word(second, 42);
        assert_eq!(u32_round_trip(second, word), word);
    }
    assert_eq!(words[0], 7);
}
