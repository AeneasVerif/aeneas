//@ [!lean] skip
//! Transmutes (the reinterpretation of the bytes of a value).
use std::mem::transmute;

fn u32_of_bytes(x: [u8; 4]) -> u32 {
    unsafe { transmute::<[u8; 4], u32>(x) }
}

fn bytes_of_u32(x: u32) -> [u8; 4] {
    unsafe { transmute::<u32, [u8; 4]>(x) }
}

fn i16_of_u16(x: u16) -> i16 {
    unsafe { transmute::<u16, i16>(x) }
}

struct Pair {
    a: u16,
    b: u16,
}

#[repr(C)]
struct Halves {
    lo: u16,
    hi: u16,
}

/// Extracted, but the model can not prove that it succeeds: the heap cells of
/// structures are typed, and the transmute requires `TypedCell Pair` and
/// `TypedCell Halves` to be equal (which can not be proved, nor disproved).
fn halves_of_pair(p: Pair) -> Halves {
    unsafe { transmute::<Pair, Halves>(p) }
}

/// Undefined behavior unless `b` is `0` or `1`.
fn bool_of_byte(b: u8) -> bool {
    unsafe { transmute::<u8, bool>(b) }
}

/// Reads a byte as a `bool` through a pointer cast: undefined behavior unless
/// it is `0` or `1`.
fn read_bool(x: &u8) -> bool {
    unsafe { *(x as *const u8 as *const bool) }
}

/// Reads the second and third bytes as a little-endian `u16`.
fn read_u16_unaligned(buf: &[u8; 4]) -> u16 {
    unsafe { (buf.as_ptr().add(1) as *const u16).read_unaligned() }
}

/// The same with an aligned read: undefined behavior if the address is odd.
/// The model only knows that the array is aligned to 1, so the read fails.
fn read_u16_misaligned(buf: &[u8; 4]) -> u16 {
    unsafe { *(buf.as_ptr().add(1) as *const u16) }
}

/// Reads the bytes of a pointer as an integer: the model does not have the
/// bytes of pointers (their cells are typed), so this fails.
fn usize_of_ptr(p: &*const u8) -> usize {
    unsafe { (p as *const *const u8 as *const usize).read_unaligned() }
}

// Undefined behaviors and reinterpretations the model rejects (see
// TransmutesSpecs.lean).

/// Rust: `buf[4]` (a `*const char` moves by 4 bytes). The model fails:
/// pointer arithmetic is only allowed over the cells of the pointee, and the
/// cells of `char` are typed.
fn char_add_over_bytes(buf: &[u8; 8]) -> u8 {
    let p = buf.as_ptr();
    unsafe { *(p.cast::<char>().add(1).cast::<u8>()) }
}

/// Rust: `a[1]`. The model fails (byte arithmetic over typed cells).
fn char_array_bytes(a: &[char; 8]) -> char {
    let p = a.as_ptr();
    unsafe { *(p.cast::<u8>().add(4).cast::<char>()) }
}

/// Rust: `1`. The model fails (typed arithmetic over byte cells).
fn char_offset_from(buf: &[u8; 8]) -> isize {
    let p = buf.as_ptr();
    unsafe { p.add(4).cast::<char>().offset_from(p.cast::<char>()) }
}

/// Rust: writes 4 zero bytes. The model fails: `write_bytes` requires byte
/// cells.
fn write_bytes_char(buf: &mut [u32; 2]) -> u8 {
    let p = buf.as_mut_ptr();
    unsafe {
        p.cast::<char>().write_bytes(0, 1);
        *p.cast::<u8>().add(1)
    }
}

/// Undefined behavior (null pointer, even for a zero-sized type): the model
/// fails.
fn read_null_zst() -> [u8; 0] {
    unsafe { core::ptr::null::<[u8; 0]>().read() }
}

fn write_bytes_zero(p: *mut u8) {
    unsafe { core::ptr::write_bytes(p, 0, 0) }
}

/// Undefined behavior (null pointer, even when no byte is written): the model
/// fails.
fn write_bytes_null() {
    write_bytes_zero(core::ptr::null_mut::<u8>())
}

fn slice_of_raw_parts(p: *const u8, len: usize) -> usize {
    unsafe { core::slice::from_raw_parts(p, len).len() }
}

/// Undefined behavior (null pointer, even for an empty slice): the model
/// fails.
fn empty_slice_of_null() -> usize {
    slice_of_raw_parts(core::ptr::null::<u8>(), 0)
}

/// Rust: `true` (`add` on a `*const ()` does not move the pointer). The model
/// fails: the comparison of two pointers into the same allocation requires the
/// cells between them to be cells of the pointee (here, bytes).
fn zst_eq(a: &[(); 4]) -> bool {
    let p = a.as_ptr();
    let q = unsafe { p.add(1) };
    p.cast::<u8>() == q.cast::<u8>()
}
