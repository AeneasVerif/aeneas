//@ [!coq] skip
//@ [coq] subdir=misc
// Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1523
// The `MIN`/`MAX` constants of every integer type must have that type.

pub fn u8_bounds() -> (u8, u8) { (u8::MIN, u8::MAX) }
pub fn u16_bounds() -> (u16, u16) { (u16::MIN, u16::MAX) }
pub fn u32_bounds() -> (u32, u32) { (u32::MIN, u32::MAX) }
pub fn u64_bounds() -> (u64, u64) { (u64::MIN, u64::MAX) }
pub fn u128_bounds() -> (u128, u128) { (u128::MIN, u128::MAX) }
pub fn i8_bounds() -> (i8, i8) { (i8::MIN, i8::MAX) }
pub fn i16_bounds() -> (i16, i16) { (i16::MIN, i16::MAX) }
pub fn i32_bounds() -> (i32, i32) { (i32::MIN, i32::MAX) }
pub fn i64_bounds() -> (i64, i64) { (i64::MIN, i64::MAX) }
pub fn i128_bounds() -> (i128, i128) { (i128::MIN, i128::MAX) }
