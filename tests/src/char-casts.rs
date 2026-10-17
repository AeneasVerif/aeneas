//@ [!lean] skip
//! Casts of characters to integers: the code point, truncated if the integer type
//! has less than 32 bits (as in unicode-ident's `ch as usize / 8`).

pub fn code_point(c: char) -> u32 {
    c as u32
}

pub fn low_byte(c: char) -> u8 {
    c as u8
}

pub fn index(c: char) -> usize {
    c as usize / 8
}

pub fn wide(c: char) -> u128 {
    1 << (c as u128 % 64)
}

pub fn signed(c: char) -> i64 {
    c as i64
}
