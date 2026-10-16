//@ [!lean] skip
//! A simplified version of the formatting functions of
//! https://github.com/dtolnay/ryu (Apache-2.0 OR BSL-1.0): we write digits to
//! an uninitialized buffer through a raw pointer, and initialize values
//! through raw pointers.
use core::mem::MaybeUninit;
use core::{ptr, slice};

// A table of all two-digit numbers (only the first ten for this test)
static DIGIT_TABLE: [u8; 20] = *b"00010203040506070809";

/// Writes the exponent `k` (with `-10 < k < 10`) to `result`, and returns the
/// number of bytes written.
pub unsafe fn write_exponent(mut k: isize, mut result: *mut u8) -> usize {
    let sign = k < 0;
    if sign {
        *result = b'-';
        result = result.add(1);
        k = -k;
    }
    *result = b'0' + k as u8;
    sign as usize + 1
}

/// Writes the two digits of `k` (with `0 <= k < 10`) to `result`.
pub unsafe fn write_two_digits(k: usize, result: *mut u8) {
    let d = DIGIT_TABLE.as_ptr().add(k * 2);
    *result = *d;
    *result.add(1) = *d.add(1);
}

/// Writes two values through raw pointers, and returns a third one (from
/// `mul_shift_all_64`, without the multiplications).
pub unsafe fn mul_shift_all(m: u64, vp: *mut u64, vm: *mut u64, mm_shift: u32) -> u64 {
    ptr::write(vp, 4 * m + 2);
    ptr::write(vm, 4 * m - 1 - mm_shift as u64);
    4 * m
}

/// The call of `mul_shift_all` in `d2d`: the outputs are uninitialized until
/// `mul_shift_all` writes them.
pub fn d2d_bounds(m: u64, mm_shift: u32) -> (u64, u64, u64) {
    let mut vp_uninit: MaybeUninit<u64> = MaybeUninit::uninit();
    let mut vm_uninit: MaybeUninit<u64> = MaybeUninit::uninit();
    let vr = unsafe {
        mul_shift_all(
            m,
            vp_uninit.as_mut_ptr(),
            vm_uninit.as_mut_ptr(),
            mm_shift,
        )
    };
    let vp = unsafe { vp_uninit.assume_init() };
    let vm = unsafe { vm_uninit.assume_init() };
    (vr, vp, vm)
}

pub struct Buffer {
    bytes: [MaybeUninit<u8>; 24],
}

impl Buffer {
    pub fn new() -> Self {
        let bytes = [MaybeUninit::<u8>::uninit(); 24];
        Buffer { bytes }
    }

    pub fn format_exponent(&mut self, k: isize) -> &[u8] {
        unsafe {
            let n = write_exponent(k, self.bytes.as_mut_ptr() as *mut u8);
            slice::from_raw_parts(self.bytes.as_ptr() as *const u8, n)
        }
    }
}

pub fn first_char_of_exponent(k: isize) -> u8 {
    let mut buf = Buffer::new();
    let s = buf.format_exponent(k);
    s[0]
}
