//@ [!lean] skip
//@ [lean] subdir=Results
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `Result` combinators (`Result::map`).
//!
//! `doubled` adapts the example of the documentation of `Result::map`
//! (<https://doc.rust-lang.org/std/result/enum.Result.html#method.map>).

pub fn doubled(num: Result<i32, ()>) -> Option<i32> {
    match num.map(|i| i * 2) {
        Ok(n) => Some(n),
        Err(..) => None,
    }
}

#[verify::test]
pub fn test_doubled() {
    assert!(matches!(doubled(Ok(1)), Some(2)));
    assert!(matches!(doubled(Ok(2)), Some(4)));
    assert!(matches!(doubled(Ok(3)), Some(6)));
    assert!(matches!(doubled(Ok(4)), Some(8)));
    assert!(matches!(doubled(Err(())), None));
}

/// A closure capturing a value.
pub fn scale(r: Result<u32, bool>, y: u32) -> Result<u32, bool> {
    r.map(move |x| x * y)
}

#[verify::test]
pub fn test_scale() {
    assert!(matches!(scale(Ok(3), 5), Ok(15)));
    assert!(matches!(scale(Err(true), 5), Err(true)));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn results() {
        test_doubled();
        test_scale();
    }
}
