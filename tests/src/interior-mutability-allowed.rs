//@ [!lean] skip
//@ [lean] aeneas-args=-allow-interior-mutability
//! The option `-allow-interior-mutability` downgrades the error of `interior-mutability-cell.rs`
//! to a warning. This only tests the option: **the generated model is unsound** (`cell_diff`
//! is translated to `ok (a = a)`), see <https://github.com/AeneasVerif/aeneas/issues/1525>.

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
