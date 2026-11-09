//@ [!lean] skip
//@ [lean] aeneas-args=-loops-to-rec

//! The memory idioms of the Zmij MWE of fournet/wip-memory-model
//! (`tests/src/raw_zmij_mwe.rs`), restricted to the primitives which Aeneas
//! models: the buffer is a `[u8; 4]` (not a `[MaybeUninit<u8>; 4]`), the table
//! is a `[u16; 2]`, and there are no pointer casts, unaligned writes, copies or
//! references made from raw pointers.
//!
//! The formatter exposes its buffer three times (`as_mut_ptr`, then `as_ptr`
//! twice), and measures the written prefix with `offset_from` between a pointer
//! of the first exposure and one of the second.

use core::slice;

/// The pairs of digits `"00"` and `"17"`, little-endian.
static PAIRS: [u16; 2] = [0x3030, 0x3731];

pub fn read_digits2(pair: usize) -> u16 {
    assert!(pair < 2);
    unsafe { *PAIRS.as_ptr().add(pair) }
}

/// Write one to three decimal digits and return the end cursor.
///
/// # Safety
/// `out` must point to at least three writable bytes in one allocation.
unsafe fn write_decimal(mut out: *mut u8, value: u8) -> *mut u8 {
    let mut remaining = value;
    unsafe {
        if remaining >= 100 {
            out.write(b'0' + remaining / 100);
            out = out.add(1);
            remaining %= 100;
        }
        if value >= 10 {
            out.write(b'0' + remaining / 10);
            out = out.add(1);
            remaining %= 10;
        }
        out.write(b'0' + remaining);
        out.add(1)
    }
}

/// A miniature integer formatter with Zmij's reusable-buffer interface.
pub struct DecimalBuffer {
    bytes: [u8; 4],
}

impl DecimalBuffer {
    pub fn new() -> Self {
        Self { bytes: [0; 4] }
    }

    /// Copy the first borrowed result before reusing the buffer.
    pub fn format_twice(buffer: &mut DecimalBuffer, first: u8, second: u8) -> (Vec<u8>, Vec<u8>) {
        let a = buffer.format(first).to_vec();
        let b = buffer.format(second).to_vec();
        (a, b)
    }

    /// Return the written decimal prefix, without allocating or copying.
    pub fn format(&mut self, value: u8) -> &[u8] {
        unsafe {
            let end = write_decimal(self.bytes.as_mut_ptr(), value);
            let len = end.offset_from(self.bytes.as_ptr()) as usize;
            slice::from_raw_parts(self.bytes.as_ptr(), len)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aligned_table() {
        for (i, bytes) in [*b"00", *b"17"].into_iter().enumerate() {
            assert_eq!(read_digits2(i), u16::from_le_bytes(bytes));
        }
    }

    #[test]
    fn repeated_buffer_exposure() {
        let mut buffer = DecimalBuffer::new();
        for value in (0..=u8::MAX).rev() {
            assert_eq!(buffer.format(value), value.to_string().as_bytes());
        }
        let mut fresh = DecimalBuffer::new();
        for (first, second) in [(255, 0), (0, 255), (10, 9), (99, 100)] {
            let (a, b) = DecimalBuffer::format_twice(&mut fresh, first, second);
            assert_eq!(a, first.to_string().as_bytes());
            assert_eq!(b, second.to_string().as_bytes());
        }
    }
}
