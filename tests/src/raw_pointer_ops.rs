//@ [!lean] skip
//@ charon-args=--opaque=crate::ext
//@ [lean] subdir=RawPointerOps
//@ [lean] aeneas-args=-split-files -all-computable

// Each unsafe wrapper forwards the corresponding std operation's preconditions.
// The opaque boundary keeps all experiment-specific descriptor plumbing local.
pub mod ext {
    pub unsafe fn read_word(p: *mut u32) -> u32 {
        p.read()
    }

    pub unsafe fn write_word(p: *mut u32, value: u32) {
        p.write(value);
    }

    pub unsafe fn read_flag(p: *mut bool) -> bool {
        p.read()
    }

    pub unsafe fn write_flag(p: *mut bool, value: bool) {
        p.write(value);
    }

    pub unsafe fn replace_word(p: *mut u32, value: u32) -> u32 {
        p.replace(value)
    }

    pub unsafe fn swap_words(p: *mut u32, q: *mut u32) {
        std::ptr::swap(p, q);
    }

    pub unsafe fn read_unaligned_word(p: *mut u32) -> u32 {
        p.read_unaligned()
    }

    pub unsafe fn write_unaligned_word(p: *mut u32, value: u32) {
        p.write_unaligned(value);
    }

    pub unsafe fn byte_advance(p: *mut u32, count: usize) -> *mut u32 {
        p.byte_add(count)
    }

    pub unsafe fn byte_shift(p: *mut u32, count: isize) -> *mut u32 {
        p.byte_offset(count)
    }

    pub unsafe fn word_distance(p: *mut u32, origin: *mut u32) -> isize {
        p.offset_from(origin)
    }

    pub unsafe fn fill_words(p: *mut u32, count: usize, value: u32) {
        std::slice::from_raw_parts_mut(p, count).fill(value);
    }
}

pub unsafe fn initialize_word(p: *mut u32, value: u32) -> u32 {
    ext::write_word(p, value);
    ext::read_word(p)
}

pub unsafe fn initialize_flag(p: *mut bool, value: bool) -> bool {
    ext::write_flag(p, value);
    ext::read_flag(p)
}

pub unsafe fn replace_word(p: *mut u32, value: u32) -> u32 {
    ext::replace_word(p, value)
}

pub unsafe fn swap_words(p: *mut u32, q: *mut u32) {
    ext::swap_words(p, q);
}

pub unsafe fn swap_self(p: *mut u32) {
    ext::swap_words(p, p);
}

pub unsafe fn read_unaligned_word(p: *mut u32) -> u32 {
    ext::read_unaligned_word(p)
}

pub unsafe fn write_unaligned_word(p: *mut u32, value: u32) {
    ext::write_unaligned_word(p, value);
}

pub unsafe fn byte_advance(p: *mut u32, count: usize) -> *mut u32 {
    ext::byte_advance(p, count)
}

pub unsafe fn byte_shift(p: *mut u32, count: isize) -> *mut u32 {
    ext::byte_shift(p, count)
}

pub unsafe fn word_distance(p: *mut u32, origin: *mut u32) -> isize {
    ext::word_distance(p, origin)
}

pub unsafe fn fill_words(p: *mut u32, count: usize, value: u32) {
    ext::fill_words(p, count, value);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_write_initializes_storage() {
        let mut storage = std::mem::MaybeUninit::<u32>::uninit();
        unsafe {
            assert_eq!(
                initialize_word(storage.as_mut_ptr(), 0x1234_5678),
                0x1234_5678
            );
            assert_eq!(storage.assume_init(), 0x1234_5678);
        }
    }

    #[test]
    fn write_does_not_read_an_invalid_old_bool() {
        let mut storage = 2u8;
        unsafe {
            assert!(initialize_flag((&mut storage as *mut u8).cast(), true));
        }
        assert_eq!(storage, 1);
    }

    #[test]
    fn replace_returns_old_value_without_dropping_it() {
        let mut word = 19u32;
        unsafe {
            assert_eq!(replace_word(&mut word, 23), 19);
        }
        assert_eq!(word, 23);
    }

    #[test]
    fn disjoint_and_identical_swaps() {
        let mut words = [11u32, 29u32, 47u32];
        let p = words.as_mut_ptr();
        unsafe {
            swap_words(p, p.add(1));
            swap_self(p);
        }
        assert_eq!(words, [29, 11, 47]);
    }

    #[test]
    fn unaligned_access_preserves_surrounding_bytes() {
        #[repr(C, align(4))]
        struct Buffer([u8; 6]);
        let mut buffer = Buffer([0xaa, 0x12, 0x34, 0x56, 0x78, 0xbb]);
        unsafe {
            let p = buffer.0.as_mut_ptr().add(1).cast::<u32>();
            assert_eq!(
                read_unaligned_word(p),
                u32::from_ne_bytes([0x12, 0x34, 0x56, 0x78])
            );
            write_unaligned_word(p, 0x8765_4321);
        }
        assert_eq!(buffer.0[0], 0xaa);
        assert_eq!(buffer.0[5], 0xbb);
        assert_eq!(&buffer.0[1..5], &0x8765_4321u32.to_ne_bytes());
    }

    #[test]
    fn byte_movement_and_signed_one_past_distance() {
        let mut words = [1u32, 2u32, 3u32];
        let p = words.as_mut_ptr();
        unsafe {
            assert_eq!(byte_advance(p, 4), p.add(1));
            assert_eq!(byte_shift(p.add(1), -4), p);
            assert_eq!(byte_advance(p, 1).cast::<u8>(), p.cast::<u8>().add(1));
            assert_eq!(word_distance(p.add(3), p), 3);
            assert_eq!(word_distance(p, p.add(3)), -3);
            assert_eq!(word_distance(p, p), 0);
        }
    }

    #[test]
    fn borrowed_subrange_restores_only_selected_words() {
        let mut words = [10u32, 20u32, 30u32, 40u32];
        unsafe {
            fill_words(words.as_mut_ptr().add(1), 2, 7);
        }
        assert_eq!(words, [10, 7, 7, 40]);
    }

    #[test]
    fn empty_range_at_one_past() {
        let mut words = [3u32];
        unsafe {
            fill_words(words.as_mut_ptr().add(1), 0, 9);
        }
        assert_eq!(words, [3]);
    }
}
