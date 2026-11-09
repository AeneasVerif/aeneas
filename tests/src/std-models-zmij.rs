//@ [!lean] skip
//! Standard library functions used by zmij: float constants, lossless integer
//! conversions, `unsigned_abs`, byte orders, `RangeInclusive::contains`.

pub fn float_consts() -> u32 {
    f64::MANTISSA_DIGITS + f32::MANTISSA_DIGITS
}

pub fn exps() -> i32 {
    f64::MAX_10_EXP - f64::MIN_10_EXP + f32::MAX_10_EXP
}

pub fn widen(x: u8) -> i64 {
    i64::from(i32::from(x))
}

pub fn abs(x: i32) -> u32 {
    x.unsigned_abs()
}

pub fn endian(x: u64, y: u16) -> u64 {
    x.to_le() ^ x.to_be() ^ (y.to_le() as u64)
}

pub fn in_range(x: i32) -> bool {
    (-5..=15).contains(&x)
}
