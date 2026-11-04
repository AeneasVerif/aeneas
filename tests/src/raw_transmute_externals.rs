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

    /// # Safety
    /// `p` must be valid for reading four initialized bytes.
    pub unsafe fn read_four(p: *mut [u8; 4]) -> [u8; 4] {
        p.read()
    }

    /// # Safety
    /// `p` must be valid for writing four bytes.
    pub unsafe fn write_four(p: *mut [u8; 4], value: [u8; 4]) {
        p.write(value);
    }

    /// # Safety
    /// `p` must support exclusive access to four initialized bytes for `'a`.
    pub unsafe fn borrow_four<'a>(p: *mut [u8; 4]) -> &'a mut [u8; 4] {
        unsafe { &mut *p }
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

/// Forms a zero-copy view: no dereference, allocation, or byte conversion.
pub fn raw_bytes_view(words: *mut u32) -> *mut [u8; 4] {
    unsafe { ext::transmute_mut::<u32, [u8; 4]>(words) }
}

/// Borrows the word's existing storage as bytes for the same lifetime.
pub fn bytes_view(word: &mut u32) -> &mut [u8; 4] {
    // Both types accept all bit patterns; the input supplies exclusive access
    // to four initialized bytes with alignment at least that of [u8; 4].
    unsafe {
        let pointer = std::ptr::from_mut(word);
        let bytes = ext::transmute_mut::<u32, [u8; 4]>(pointer);
        ext::borrow_four(bytes)
    }
}

pub unsafe fn array_pointer_round_trip(words: *mut u32) -> *mut u32 {
    ext::transmute_mut::<[u8; 4], u32>(raw_bytes_view(words))
}

/// # Safety
/// `words` must be valid for reading an initialized, properly aligned u32.
pub unsafe fn read_word_bytes(words: *mut u32) -> [u8; 4] {
    ext::read_four(raw_bytes_view(words))
}

/// # Safety
/// `words` must be valid for reading and writing a properly aligned u32.
pub unsafe fn overwrite_word_bytes(words: *mut u32, bytes: [u8; 4]) -> u32 {
    ext::write_four(raw_bytes_view(words), bytes);
    ext::read_word(words)
}

#[test]
fn zero_copy_array_view() {
    for initial in [0u32, 0x01020304, u32::MAX] {
        let mut words = [7u32, initial];
        unsafe {
            let second = words.as_mut_ptr().add(1);
            assert_eq!(raw_bytes_view(second).cast::<u32>(), second);
            assert_eq!(array_pointer_round_trip(second), second);
            assert_eq!(read_word_bytes(second), initial.to_ne_bytes());
            for bytes in [[0, 0, 0, 0], [1, 2, 3, 4], [255, 254, 253, 252]] {
                let expected = u32::from_ne_bytes(bytes);
                assert_eq!(overwrite_word_bytes(second, bytes), expected);
                assert_eq!(ext::read_word(second), expected);
                assert_eq!(read_word_bytes(second), bytes);
            }
        }
        assert_eq!(words[0], 7);
        assert_eq!(words[1], u32::from_ne_bytes([255, 254, 253, 252]));
    }
}

#[test]
fn mutable_borrow_view() {
    let mut words = [7u32, 0x01020304];
    let original_address = std::ptr::addr_of_mut!(words[1]).cast::<u8>();
    let view = bytes_view(&mut words[1]);
    assert_eq!(view.as_mut_ptr(), original_address);
    assert_eq!(*view, 0x01020304u32.to_ne_bytes());
    *view = [1, 2, 3, 4];
    assert_eq!(words, [7, u32::from_ne_bytes([1, 2, 3, 4])]);
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
