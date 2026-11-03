//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `Vec` methods (`Vec::clear`), verifying the model matches Rust behavior.

/// The example from the documentation of `Vec::clear`
/// (<https://doc.rust-lang.org/std/vec/struct.Vec.html#method.clear>).
#[verify::test]
pub fn test_vec_clear_doc() {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);

    v.clear();

    assert!(v.len() == 0);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vec_clear_doc() {
        test_vec_clear_doc();
    }
}
