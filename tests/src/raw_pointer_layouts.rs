//@ [!lean] skip
//! Byte representations computed from the layouts chosen by rustc.

/// The alignment of the table is larger than that of its elements: we can read
/// it as `u16`s.
#[repr(C, align(2))]
struct Digits2([u8; 4]);

static DIGITS2: Digits2 = Digits2(*b"0102");

unsafe fn digits2(value: usize) -> &'static u16 {
    &*DIGITS2.0.as_ptr().cast::<u16>().add(value)
}

/// A structure with padding (rustc reorders the fields).
#[derive(Copy, Clone)]
struct Mixed {
    a: u8,
    b: u64,
    c: u16,
}

fn read_mixed(xs: &[Mixed], i: usize) -> u64 {
    let m = unsafe { *xs.as_ptr().add(i) };
    m.b
}
