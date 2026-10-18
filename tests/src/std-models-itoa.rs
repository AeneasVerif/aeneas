//@ [!lean] skip
//! Standard library functions used by itoa: `ilog10`, `TryFrom<i32>` for the
//! unsigned types, `str::len`.

pub fn digits(x: u64) -> u32 {
    if x == 0 {
        1
    } else {
        x.ilog10() + 1
    }
}

pub fn digits_signed(x: i32) -> u32 {
    if x <= 0 {
        1
    } else {
        x.ilog10() + 1
    }
}

pub fn to_u8(x: i32) -> u8 {
    match u8::try_from(x) {
        Ok(y) => y,
        Err(_) => 0,
    }
}

pub fn length(s: &str) -> usize {
    s.len()
}
