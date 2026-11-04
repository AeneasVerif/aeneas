//@ [!lean] skip
//@ [lean] aeneas-args=-loops-to-rec -split-files
//@ [lean] subdir=RawZeroize

//! Standalone adaptation of zeroize 1.9.1's MaybeUninit-slice implementation
//! and volatile_set helper (MIT OR Apache-2.0, RustCrypto Developers).
//! Reference: https://docs.rs/zeroize/1.9.1/src/zeroize/lib.rs.html#419-442
//! The helper is inlined and specialized to u8. See tests/lean/EXTRACTION.md
//! for the explicit heap-backed MaybeUninit slice model and Lean adaptations.

use core::mem::MaybeUninit;

/// Zero every byte, including padding, without reading an old value of T.
/// The result is initialized bytes, not necessarily a valid T. Calling
/// assume_init afterward still requires establishing T's validity.
pub fn zeroize<T>(storage: &mut [MaybeUninit<T>]) {
    let bytes = storage.as_mut_ptr().cast::<u8>();
    let size = storage
        .len()
        .checked_mul(core::mem::size_of::<T>())
        .expect("overflow");
    assert!(size <= isize::MAX as usize);
    for i in 0..size {
        // The exclusive slice supplies the entire checked range; u8 needs
        // no stronger alignment or initialized old value.
        let p = unsafe { bytes.add(i) };
        unsafe { core::ptr::write_volatile(p, 0) };
    }
}

/// All-zero bytes form a valid u32; the mutable reference can be returned.
pub fn zeroize_word(word: &mut u32) {
    let ptr = core::ptr::from_mut(word).cast::<MaybeUninit<u32>>();
    // Same size/alignment as u32, exclusive for this call. Zero is a valid u32,
    // so the original reference is usable again after the temporary slice ends.
    let storage = unsafe { core::slice::from_raw_parts_mut(ptr, 1) };
    zeroize(storage);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn padding_and_uninitialized_storage() {
        #[repr(C)]
        struct Padded {
            _tag: u8,
            _word: u32,
        }
        let mut storage = [MaybeUninit::<Padded>::uninit(), MaybeUninit::uninit()];
        zeroize(&mut storage);
        unsafe {
            let bytes = core::slice::from_raw_parts(
                storage.as_ptr().cast::<u8>(),
                core::mem::size_of_val(&storage),
            );
            assert!(bytes.iter().all(|&b| b == 0));
        }
        let mut nonzero = [MaybeUninit::<core::num::NonZeroU32>::uninit()];
        zeroize(&mut nonzero);
        unsafe {
            let bytes = core::slice::from_raw_parts(
                nonzero.as_ptr().cast::<u8>(),
                core::mem::size_of_val(&nonzero),
            );
            assert!(bytes.iter().all(|&b| b == 0));
        }
        // Never assume_init the NonZeroU32: initialized bytes need not be a valid T.
    }

    #[test]
    fn typed_result_and_neighbors() {
        let mut words = [17, u32::MAX, 23];
        zeroize_word(&mut words[1]);
        assert_eq!(words, [17, 0, 23]);
        let mut storage = words.map(MaybeUninit::new);
        zeroize(&mut storage);
        assert_eq!(storage.map(|word| unsafe { word.assume_init() }), [0; 3]);
    }

    #[test]
    fn empty_and_zero_sized_ranges() {
        zeroize::<u32>(&mut []);
        zeroize(&mut [MaybeUninit::<()>::uninit(); 7]);
    }
}
