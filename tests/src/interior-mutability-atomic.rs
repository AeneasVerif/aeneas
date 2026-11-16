//@ [lean] known-failure
//@ [!lean] skip
//! Same as `interior-mutability-cell.rs`, with an atomic: the two calls to `fetch_add(&self, ...)`
//! were merged, and the false theorem `atomic_diff = ok true` could be proved.
//!
//! See <https://github.com/AeneasVerif/aeneas/issues/1525>.

use std::sync::atomic::{AtomicU32, Ordering::SeqCst};

pub fn atomic_diff() -> bool {
    let a = AtomicU32::new(0);
    let x = a.fetch_add(1, SeqCst);
    let y = a.fetch_add(1, SeqCst);
    x == y
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atomic_diff_is_false() {
        assert!(!atomic_diff());
    }
}
