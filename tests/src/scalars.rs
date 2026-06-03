//@ [!lean] skip

fn u32_use_wrapping_add(x: u32, y: u32) -> u32 {
    x.wrapping_add(y)
}

fn i32_use_wrapping_add(x: i32, y: i32) -> i32 {
    x.wrapping_add(y)
}

fn u32_use_wrapping_sub(x: u32, y: u32) -> u32 {
    x.wrapping_sub(y)
}

fn i32_use_wrapping_sub(x: i32, y: i32) -> i32 {
    x.wrapping_sub(y)
}

fn u32_use_shift_right(x: u32) -> u32 {
    x >> 2
}

fn i32_use_shift_right(x: i32) -> i32 {
    x >> 2
}

fn u32_use_shift_left(x: u32) -> u32 {
    x << 2
}

fn i32_use_shift_left(x: i32) -> i32 {
    x << 2
}

fn u32_use_wrapping_shl(x: u32, s: u32) -> u32 {
    x.wrapping_shl(s)
}

fn i32_use_wrapping_shl(x: i32, s: u32) -> i32 {
    x.wrapping_shl(s)
}

fn u32_use_wrapping_shr(x: u32, s: u32) -> u32 {
    x.wrapping_shr(s)
}

fn i32_use_wrapping_shr(x: i32, s: u32) -> i32 {
    x.wrapping_shr(s)
}

/// Regression test for issue #816: shifts assigned through a dereferenced pointer
/// (here via `IndexMut`) reach Aeneas with overflow mode `OWrap` (Charon issue
/// #1041), so the Lean extraction must route them through `Std.U64.wrapping_shr`
/// rather than the undefined `U64.shr`.
fn shr_into_index_mut(x: u64, out: &mut [u64; 2]) {
    out[0] = x >> 20;
}

/// Counterpart to `shr_into_index_mut` for `<<`.
fn shl_into_index_mut(x: u64, out: &mut [u64; 2]) {
    out[0] = x << 20;
}

fn add_and(a: u32, b: u32) -> u32 {
    (b & a) + (b & a)
}

fn u32_use_rotate_right(x: u32) -> u32 {
    x.rotate_right(2)
}

fn i32_use_rotate_right(x: i32) -> i32 {
    x.rotate_right(2)
}

fn u32_use_rotate_left(x: u32) -> u32 {
    x.rotate_left(2)
}

fn i32_use_rotate_left(x: i32) -> i32 {
    x.rotate_left(2)
}

fn u32_default() -> u32 {
    Default::default()
}

fn i32_default() -> i32 {
    Default::default()
}

fn match_usize(x: usize) -> bool {
    match x {
        0 | 1 | 2 => true,
        x => false,
    }
}

fn match_isize(x: isize) -> isize {
    match x {
        0 | -1 | 2 => 0,
        y => y + 1,
    }
}

fn u32_as_u16(x: u32) -> u16 {
    x as u16
}

fn u16_as_u32(x: u16) -> u32 {
    x as u32
}

fn u32_as_i16(x: u32) -> i16 {
    x as i16
}

fn i16_as_u32(x: i16) -> u32 {
    x as u32
}

pub fn u32_use_bits() -> u32 {
    u32::BITS
}

pub fn i32_use_bits() -> u32 {
    i32::BITS
}
