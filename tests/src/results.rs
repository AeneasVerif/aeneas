//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `Result` combinators (`Result::map`), verifying the model matches Rust behavior.

/// What the example in the documentation of `Result::map`
/// (<https://doc.rust-lang.org/std/result/enum.Result.html#method.map>) prints for one line:
/// ```text
/// match num.parse::<i32>().map(|i| i * 2) {
///     Ok(n) => println!("{n}"),
///     Err(..) => {}
/// }
/// ```
/// String parsing and printing have no Lean models, so this takes the result of `parse` and
/// returns what is printed.
pub fn doc_line(num: Result<i32, ()>) -> Option<i32> {
    match num.map(|i| i * 2) {
        Ok(n) => Some(n),
        Err(..) => None,
    }
}

/// The doc example parses the lines of `"1\n2\n3\n4\n"` and prints `2`, `4`, `6`, `8`; a line which
/// doesn't parse prints nothing.
#[verify::test]
pub fn test_result_map_doc() {
    assert!(matches!(doc_line(Ok(1)), Some(2)));
    assert!(matches!(doc_line(Ok(2)), Some(4)));
    assert!(matches!(doc_line(Ok(3)), Some(6)));
    assert!(matches!(doc_line(Ok(4)), Some(8)));
    assert!(matches!(doc_line(Err(())), None));
}

/// The closure captures a value.
pub fn result_map_capture(r: Result<u32, bool>, y: u32) -> Result<u32, bool> {
    r.map(move |x| x * y)
}

#[verify::test]
pub fn test_result_map_capture() {
    assert!(matches!(result_map_capture(Ok(3), 5), Ok(15)));
    assert!(matches!(result_map_capture(Err(true), 5), Err(true)));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn result_map_doc() {
        test_result_map_doc();
    }

    #[test]
    fn result_map_capture() {
        test_result_map_capture();
    }
}
