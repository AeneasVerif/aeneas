//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-loops-to-rec

//! Minimal memory idioms from PR #1455 at d613188e, not the Zmij algorithm.
//! Native-endian results are explicit; Lean instantiates a little-endian target.

use core::{mem::MaybeUninit, ptr, slice};

#[repr(C, align(2))]
struct AlignedPairs([u8; 4]);

static PAIRS: AlignedPairs = AlignedPairs(*b"0017");

pub fn digits2(pair: usize) -> &'static u16 {
    assert!(pair < 2);
    // The enclosing static supplies the alignment, not the u8 element type.
    unsafe { &*PAIRS.0.as_ptr().cast::<u16>().add(pair) }
}

pub fn read_digits2(pair: usize) -> u16 {
    assert!(pair < 2);
    unsafe { *PAIRS.0.as_ptr().cast::<u16>().add(pair) }
}

pub fn write_digits(buffer: &mut [u8; 10], digits: u64) {
    // At most eight bytes are written; both outside bytes remain unchanged.
    unsafe {
        buffer
            .as_mut_ptr()
            .add(1)
            .cast::<u64>()
            .write_unaligned(digits)
    };
}

pub fn write_exponent_data(buffer: &mut [u8; 7], data: u64) {
    unsafe {
        ptr::copy_nonoverlapping(
            ptr::addr_of!(data).cast::<u8>(),
            buffer.as_mut_ptr().add(1),
            5,
        );
    }
}

pub fn write_exponent(buffer: &mut [u8; 5], digits: u16, sign: u16, overlap: bool) {
    unsafe {
        let p = buffer.as_mut_ptr();
        // Include the one-byte overlap used for a single-digit exponent.
        p.add(if overlap { 1 } else { 2 })
            .cast::<u16>()
            .write_unaligned(digits);
        p.cast::<u16>().write_unaligned(sign);
    }
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
    bytes: [MaybeUninit<u8>; 4],
}

impl DecimalBuffer {
    pub fn new() -> Self {
        Self {
            bytes: [MaybeUninit::uninit(); 4],
        }
    }

    /// Return only the initialized decimal prefix, without allocating or copying.
    pub fn format(&mut self, value: u8) -> &[u8] {
        unsafe {
            let end = write_decimal(self.bytes.as_mut_ptr().cast::<u8>(), value);
            let len = end.offset_from(self.bytes.as_ptr().cast::<u8>()) as usize;
            // The writer initializes exactly this prefix; the rest is not read.
            slice::from_raw_parts(self.bytes.as_ptr().cast::<u8>(), len)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aligned_table() {
        for (i, bytes) in [*b"00", *b"17"].into_iter().enumerate() {
            assert_eq!(read_digits2(i), u16::from_ne_bytes(bytes));
            assert_eq!(*digits2(i), u16::from_ne_bytes(bytes));
        }
    }

    #[test]
    fn unaligned_write_and_local_copy() {
        for word in [0, u64::MAX, 0x0123_4567_89ab_cdef] {
            let mut buffer = [0xa5; 10];
            write_digits(&mut buffer, word);
            assert_eq!(&buffer[1..9], &word.to_ne_bytes());
            assert_eq!((buffer[0], buffer[9]), (0xa5, 0xa5));
            let mut output = [0x5a; 7];
            write_exponent_data(&mut output, word);
            assert_eq!(&output[1..6], &word.to_ne_bytes()[..5]);
            assert_eq!((output[0], output[6]), (0x5a, 0x5a));
        }
    }

    #[test]
    fn overlapping_and_disjoint_writes() {
        for overlap in [false, true] {
            let mut buffer = [0xa5; 5];
            let digits = u16::from_ne_bytes(*b"17");
            let sign = u16::from_ne_bytes(*b"e+");
            write_exponent(&mut buffer, digits, sign, overlap);
            assert_eq!(
                buffer,
                if overlap {
                    [b'e', b'+', b'7', 0xa5, 0xa5]
                } else {
                    [b'e', b'+', b'1', b'7', 0xa5]
                }
            );
        }
    }

    #[test]
    fn repeated_buffer_exposure() {
        let mut buffer = DecimalBuffer::new();
        for value in (0..=u8::MAX).rev() {
            assert_eq!(buffer.format(value), value.to_string().as_bytes());
        }
        let mut fresh = DecimalBuffer::new();
        assert_eq!(fresh.format(0), b"0");
    }
}
