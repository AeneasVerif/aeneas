//@ [!lean] skip
//! The memory idioms of the upstream Ryu and Zmij crates: `MaybeUninit` out-parameters and buffers,
//! pointer casts, `sub`, copies, `write_bytes`, unaligned writes, raw borrows of places, shared
//! reborrows of values behind raw pointers, globals which read constant tables through raw
//! pointers, and `size_of` in generic code.
#![allow(clippy::missing_safety_doc)]
use core::mem::{self, MaybeUninit};
use core::ptr;
use core::slice;

/// Ryu's `mul_shift_all`: writes its outputs through raw pointers.
pub unsafe fn out_parameters(m: u64, vp: *mut u64, vm: *mut u64) -> u64 {
    ptr::write(vp, 4 * m + 2);
    ptr::write(vm, 4 * m - 1);
    4 * m
}

/// Ryu's `d2d`: the outputs are uninitialized until `out_parameters` writes them.
pub fn initialized_outputs(m: u64) -> (u64, u64, u64) {
    assert!(m < 1000);
    let mut vp: MaybeUninit<u64> = MaybeUninit::uninit();
    let mut vm: MaybeUninit<u64> = MaybeUninit::uninit();
    let vr = unsafe { out_parameters(m, vp.as_mut_ptr(), vm.as_mut_ptr()) };
    let vp = unsafe { vp.assume_init() };
    let vm = unsafe { vm.assume_init() };
    (vr, vp, vm)
}

static DIGITS: [u8; 8] = *b"00010203";

/// Ryu's `write_exponent`: copies from a table, backwards from the end of the output.
pub unsafe fn write_two_digits(k: usize, result: *mut u8) -> *mut u8 {
    let d = DIGITS.as_ptr().add(k * 2);
    let result = result.sub(2);
    ptr::copy_nonoverlapping(d, result, 2);
    result
}

/// The buffer of Ryu and Zmij: uninitialized bytes, written through a `*mut u8` and read back with
/// `from_raw_parts`.
pub struct Buffer {
    bytes: [MaybeUninit<u8>; 8],
}

impl Buffer {
    pub fn new() -> Self {
        let bytes = [MaybeUninit::<u8>::uninit(); 8];
        Buffer { bytes }
    }

    pub fn format(&mut self, k: usize) -> &[u8] {
        assert!(k < 4);
        unsafe {
            let start = self.bytes.as_mut_ptr().cast::<u8>();
            let end = write_two_digits(k, start.add(4));
            let len = 4 - end.offset_from(start) as usize;
            let _ = len;
            slice::from_raw_parts(self.bytes.as_ptr().cast::<u8>().add(2), 2)
        }
    }
}

/// Zmij's `write`: moves the digits, pads with zeros, and writes a pair of bytes unaligned.
pub fn shift_and_pad(x: u8) -> [u8; 6] {
    let mut buf = [x, 1, 2, 3, 4, 5];
    unsafe {
        let p = buf.as_mut_ptr();
        ptr::copy(p.add(1), p, 3);
        ptr::write_bytes(p.add(3), b'0', 2);
        p.add(1).cast::<u16>().write_unaligned(0x3938u16.to_le());
    }
    buf
}

/// Zmij's `ptr::addr_of!(exp_data)`: a raw borrow of a local, then a byte copy.
pub fn copy_from_local(v: u32) -> [u8; 4] {
    let data = v.to_le();
    let mut out = [0u8; 4];
    unsafe {
        ptr::copy_nonoverlapping(ptr::addr_of!(data).cast::<u8>(), out.as_mut_ptr(), 4);
    }
    out
}

/// Zmij's exponent path: the length of the copy is computed after the raw borrow (the exposure must
/// stay alive until the copy).
pub unsafe fn copy_from_local_len(v: u32, long: bool, buffer: *mut u8) {
    let data = v.to_le();
    ptr::copy_nonoverlapping(
        ptr::addr_of!(data).cast::<u8>(),
        buffer,
        if long { 4 } else { 3 },
    );
}

static PAIRS: [u8; 4] = *b"1234";

/// Zmij's `digits2`: a shared reborrow of a value behind a raw pointer.
pub unsafe fn pair(i: usize) -> &'static u8 {
    &*PAIRS.as_ptr().add(i)
}

pub fn read_pair(i: usize) -> u8 {
    assert!(i < 4);
    unsafe { *pair(i) }
}

pub struct Table {
    first: u8,
    second: u8,
}

const fn compute_table() -> Table {
    unsafe {
        Table {
            first: *PAIRS.as_ptr(),
            second: *PAIRS.as_ptr().add(1),
        }
    }
}

/// Zmij's `STATIC_DATA`: a global whose initializer reads a table through a raw pointer.
static TABLE: Table = compute_table();

/// Zmij's `let d = ptr::addr_of!(STATIC_DATA); let d = &*d;`.
pub fn read_table() -> u8 {
    let d = ptr::addr_of!(TABLE);
    let d = unsafe { &*d };
    d.first + d.second
}

/// Zmij's `mem::size_of::<UInt>()` in generic code.
pub fn num_bits<T>() -> usize {
    mem::size_of::<T>() * 8
}

pub fn num_bits_u32() -> usize {
    num_bits::<u32>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn idioms() {
        assert_eq!(initialized_outputs(1), (4, 6, 3));
        let mut b = Buffer::new();
        assert_eq!(b.format(1), b"01");
        assert_eq!(shift_and_pad(b'x'), [1, b'8', b'9', b'0', b'0', 5]);
        assert_eq!(copy_from_local(0x04030201), [1, 2, 3, 4]);
        let mut out = [0u8; 4];
        unsafe { copy_from_local_len(0x04030201, false, out.as_mut_ptr()) };
        assert_eq!(out, [1, 2, 3, 0]);
        assert_eq!(read_pair(2), b'3');
        assert_eq!(read_table(), b'1' + b'2');
        assert_eq!(num_bits_u32(), 32);
    }
}
