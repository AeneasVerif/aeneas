//@ [!lean] skip
//! A simplified version of the formatting functions of
//! https://github.com/dtolnay/ryu (Apache-2.0 OR BSL-1.0): we write digits to
//! a buffer through a raw pointer.

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

pub struct Buffer {
    bytes: [u8; 24],
}

impl Buffer {
    pub fn new() -> Self {
        Buffer { bytes: [0; 24] }
    }

    pub fn format_exponent(&mut self, k: isize) -> &[u8] {
        unsafe {
            let n = write_exponent(k, self.bytes.as_mut_ptr());
            core::slice::from_raw_parts(self.bytes.as_ptr(), n)
        }
    }
}

pub fn first_char_of_exponent(k: isize) -> u8 {
    let mut buf = Buffer::new();
    let s = buf.format_exponent(k);
    s[0]
}
