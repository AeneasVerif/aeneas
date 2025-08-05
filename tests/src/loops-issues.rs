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
