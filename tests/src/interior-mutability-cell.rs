//@ [lean] known-failure
//@ [!lean] skip
//! Aeneas translates a shared reference as an immutable value. This is unsound for the types with
//! interior mutability: `Cell::set(&self, ...)` modifies the cell behind the reference, but the
//! generated function can't return the new value of the cell. We used to translate `cell_diff`
//! to `ok (a = a)`, and the false theorem `cell_diff = ok true` could be proved. We now reject the
//! code which uses such references.
//!
//! See <https://github.com/AeneasVerif/aeneas/issues/1525>.

use std::cell::Cell;

pub fn cell_diff() -> bool {
    let c = Cell::new(0u32);
    let a = c.get();
    c.set(1);
    let b = c.get();
    a == b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cell_diff_is_false() {
        assert!(!cell_diff());
    }
}
