//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub fn f64_id(x: f64) -> f64 {
    x
}

pub fn f64_add(x: f64, y: f64) -> f64 {
    x + y
}

pub fn f64_sub(x: f64, y: f64) -> f64 {
    x - y
}

pub fn f64_mul(x: f64, y: f64) -> f64 {
    x * y
}

pub fn f64_div(x: f64, y: f64) -> f64 {
    x / y
}

pub fn f64_rem(x: f64, y: f64) -> f64 {
    x % y
}

pub fn f64_neg(x: f64) -> f64 {
    -x
}

pub fn f64_literal() -> f64 {
    let x = 1.0f64;
    let y = 1.5f64;
    x + y
}

pub fn f64_le(x: f64, y: f64) -> bool {
    x <= y
}

pub fn f64_eq(x: f64, y: f64) -> bool {
    x == y
}

pub fn f64_ne(x: f64, y: f64) -> bool {
    x != y
}

pub fn f32_add(x: f32, y: f32) -> f32 {
    x + y
}

pub fn f32_literal() -> f32 {
    1.25f32
}

pub fn u32_to_f32(x: u32) -> f32 {
    x as f32
}

pub fn i32_to_f64(x: i32) -> f64 {
    x as f64
}

pub fn f32_to_f64(x: f32) -> f64 {
    x as f64
}

pub fn f64_to_f32(x: f64) -> f32 {
    x as f32
}

pub fn f64_to_u64(x: f64) -> u64 {
    x as u64
}

#[verify::test]
pub fn test_f64_arithmetic() {
    assert!(f64_add(1.0, 2.0) == 3.0);
    assert!(f64_sub(5.0, 2.0) == 3.0);
    assert!(f64_mul(1.5, 2.0) == 3.0);
    assert!(f64_div(6.0, 2.0) == 3.0);
    assert!(f64_neg(3.0) == -3.0);
    assert!(f64_literal() == 2.5);
}

#[verify::test]
pub fn test_f64_comparisons() {
    assert!(f64_le(1.0, 1.0));
    assert!(f64_le(1.0, 2.0));
    assert!(f64_eq(3.0, 3.0));
    assert!(f64_ne(3.0, 4.0));
    assert!(!f64_eq(3.0, 4.0));
}

#[verify::test]
pub fn test_f32_arithmetic() {
    assert!(f32_add(1.0, 2.0) == 3.0);
    assert!(f32_literal() == 1.25);
}

#[verify::test]
pub fn test_float_casts() {
    assert!(u32_to_f32(3) == 3.0);
    assert!(i32_to_f64(-3) == -3.0);
    assert!(f32_to_f64(1.5) == 1.5);
    assert!(f64_to_f32(1.5) == 1.5);
}
