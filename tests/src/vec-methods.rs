//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `Vec` methods (`Vec::is_empty`), verifying the model matches Rust behavior.

/// The example from the documentation of `Vec::is_empty`
/// (<https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty>).
#[verify::test]
pub fn test_vec_is_empty_doc() {
    let mut v = Vec::new();
    assert!(v.is_empty());

    v.push(1);
    assert!(!v.is_empty());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vec_is_empty_doc() {
        test_vec_is_empty_doc();
    }
}
