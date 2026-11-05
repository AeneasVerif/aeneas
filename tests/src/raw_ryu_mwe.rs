//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-loops-to-rec

//! Minimal memory idioms from PR #1455 at d613188e, not the Ryu algorithm.
//! See tests/lean/EXTRACTION.md for extraction and heap-boundary limitations.

use core::{mem::MaybeUninit, ptr, slice};

/// # Safety
/// Both output pointers must be writable, aligned, and disjoint for one u64.
pub unsafe fn out_parameters(a: u64, b: u64, first: *mut u64, second: *mut u64) {
    unsafe {
        ptr::write(first, a);
        ptr::write(second, b);
    }
}

pub fn initialized_outputs(a: u64, b: u64) -> (u64, u64) {
    let mut first = MaybeUninit::<u64>::uninit();
    let mut second = MaybeUninit::<u64>::uninit();
    unsafe {
        out_parameters(a, b, first.as_mut_ptr(), second.as_mut_ptr());
        (first.assume_init(), second.assume_init())
    }
}

/// Initialize only the prefix; never observe the uninitialized suffix.
pub fn buffer_as(a: u8, b: u8) -> [u8; 2] {
    let mut storage = [MaybeUninit::<u8>::uninit(); 4];
    unsafe {
        let p = storage.as_mut_ptr() as *mut u8;
        p.write(a);
        p.add(1).write(b);
        let bytes = slice::from_raw_parts(storage.as_ptr() as *const u8, 2);
        [bytes[0], bytes[1]]
    }
}

pub fn buffer_cast(a: u8, b: u8) -> [u8; 2] {
    let mut storage = [MaybeUninit::<u8>::uninit(); 4];
    unsafe {
        let p = storage.as_mut_ptr().cast::<u8>();
        p.write(a);
        p.add(1).write(b);
        let bytes = slice::from_raw_parts(storage.as_ptr().cast::<u8>(), 2);
        [bytes[0], bytes[1]]
    }
}

static PAIRS: [u8; 4] = *b"0017";

pub fn copy_table(pair: usize) -> [u8; 2] {
    assert!(pair < 2);
    let mut output = [0; 2];
    unsafe {
        ptr::copy_nonoverlapping(PAIRS.as_ptr().add(2 * pair), output.as_mut_ptr(), 2);
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn out_parameters_and_prefix() {
        for (a, b) in [(0, 0), (1, u64::MAX), (u64::MAX, 17)] {
            assert_eq!(initialized_outputs(a, b), (a, b));
        }
        for (a, b) in [(0, 255), (17, 42), (255, 0)] {
            assert_eq!(buffer_as(a, b), [a, b]);
            assert_eq!(buffer_cast(a, b), [a, b]);
        }
    }

    #[test]
    fn table_copy() {
        assert_eq!(copy_table(0), *b"00");
        assert_eq!(copy_table(1), *b"17");
    }
}
