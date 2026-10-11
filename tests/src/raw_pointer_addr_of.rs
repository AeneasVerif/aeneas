//@ [!lean] skip
//! Raw pointers to places.
use std::ptr;

/// Copy the first bytes of an integer to a buffer (from zmij).
unsafe fn write_bytes_of(v: u64, buffer: *mut u8) {
    let data = v;
    ptr::copy_nonoverlapping(ptr::addr_of!(data).cast::<u8>(), buffer, 5);
}

fn local_through_raw() -> u32 {
    let mut x = 1u32;
    let p = &raw mut x;
    unsafe { *p = 2 };
    x
}

fn incr_through_raw(x: &mut u32) {
    let p = &raw mut *x;
    unsafe { *p = *p + 1 };
}

fn field_through_raw(x: &mut (u32, u16)) -> u16 {
    let p = &raw const x.1;
    unsafe { *p }
}

fn copy_through_raw(p: *mut u32) -> *const u32 {
    unsafe { &raw const *p }
}

static TABLE: [u16; 4] = [1, 2, 3, 4];

fn read_static(i: usize) -> u16 {
    let p = ptr::addr_of!(TABLE).cast::<u16>();
    if i < 4 {
        unsafe { *p.add(i) }
    } else {
        0
    }
}
