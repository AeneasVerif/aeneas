//@ [!lean] skip
//! Exercise the translation of loops on examples which proved to be problematic.

/// Dummy helper
fn write(_: &mut [u8; 4]) {}

/// Dummy helper
fn read(_: &[u8; 4]) {}

const CARRAY: [u16; 4] = [0, 0, 0, 0];

/// This comes from an issue found in SymCrust and minimized
fn loop_access_array(k: usize) {
    let mut start = 0usize;
    while start < 4 {
        let _: u16 = CARRAY[k];
        start += 1;
    }
}

/// This comes from an issue found in SymCrust and minimized
fn loop_array_len(b: bool) {
    let buf = [0u8; 4];
    let _: usize = buf.len();

    while b {
        let _ = buf.len();
    }
}

/// This comes from an issue found in SymCrust and minimized
fn loop_array_len_write(b0: bool, b1: bool) {
    let mut buf = [0u8; 4];
    let _: usize = buf.len();

    while b0 {
        if b1 {
            write(&mut buf);
        }
    }
}

const MAX_NROWS: usize = 4;

/// This comes from an issue found in SymCrust and minimized
fn read_global_loop(b: bool, n_rows: usize) {
    debug_assert!(n_rows <= MAX_NROWS);
    while b {}
}

#[allow(unused_comparisons)]
fn mut_loop_len(_: &mut u32, b: bool) {
    let buf = [0u8; 4];

    while b {
        debug_assert!(0 <= buf.len());
    }
}

/// This comes from an issue found in SymCrust and minimized
fn test(b0: bool, b1: bool) {
    let mut buf = [0u8; 4];
    let _ = buf.len();

    while b0 {
        if b1 {
            write(&mut buf);
        }

        let _ = read(&buf);
    }
}
