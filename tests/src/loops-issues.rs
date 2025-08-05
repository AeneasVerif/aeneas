//@ [!lean] skip
//! Exercise the translation of loops on examples which proved to be problematic.

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
fn loop_array_len()
{
    let buf = [0u8; 4];
    let _: usize = buf.len();

    loop
    {
        let _ = buf.len();
    }
}

fn write(a : &mut [u8; 4]) { a[0] = 0 }

/// This comes from an issue found in SymCrust and minimized
fn loop_array_len_write(b : bool)
{
    let mut buf = [0u8; 4];
    let _: usize = buf.len();

    loop
    {
        if b
        {
            write (&mut buf);
        }
    }
}

const MAX_NROWS: usize = 4;

/// This comes from an issue found in SymCrust and minimized
fn read_global_loop(n_rows: usize)
{
    debug_assert!(n_rows <= MAX_NROWS);
    loop {}
}

fn mut_loop_len(_: &mut u32)
{
    let buf = [0u8; 8];

    loop
    {
        debug_assert!(0 <= buf.len());
    }
}
