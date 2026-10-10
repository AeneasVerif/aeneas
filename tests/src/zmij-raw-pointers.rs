//@ [!lean] skip
//! A simplified version of https://github.com/dtolnay/zmij (MIT): tables read
//! through raw pointers, and digits written through raw pointers.
#![allow(non_camel_case_types)]

#[derive(Copy, Clone)]
struct uint128 {
    hi: u64,
    lo: u64,
}

const POW10_MINOR: [u64; 4] = [1, 10, 100, 1000];

const POW10_MAJOR: [uint128; 2] = [uint128 { hi: 0, lo: 1 }, uint128 { hi: 1, lo: 0 }];

fn pow10_minor(i: usize) -> u64 {
    unsafe { *POW10_MINOR.as_ptr().add(i) }
}

fn pow10_major(i: usize) -> uint128 {
    unsafe { *POW10_MAJOR.as_ptr().add(i) }
}

/// Writes `n` zeros through `p`.
unsafe fn write_zeros(p: *mut u8, n: usize) {
    let mut i = 0;
    while i < n {
        *p.add(i) = b'0';
        i += 1;
    }
}

/// Writes the digit `d` followed by a dot.
unsafe fn write_digit_dot(p: *mut u8, d: u8) -> *mut u8 {
    *p = b'0' + d;
    *p.add(1) = b'.';
    p.add(2)
}

pub fn format_small(d: u8, buf: &mut [u8; 8]) -> usize {
    unsafe {
        let start = buf.as_mut_ptr();
        let end = write_digit_dot(start, d);
        write_zeros(end, 2);
        4
    }
}
