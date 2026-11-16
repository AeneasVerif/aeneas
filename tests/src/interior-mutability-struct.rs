//@ [lean] known-failure
//@ [!lean] skip
//! Same as `interior-mutability-cell.rs`, with a user-defined type which contains a `Cell`: the
//! methods which take `&self` modify the type, so shared references to `Counter` are rejected too
//! (we used to merge the two calls to `incr(&self)`, and to prove `two_increments = ok 0`).
//!
//! See <https://github.com/AeneasVerif/aeneas/issues/1525>.

use std::cell::Cell;

pub struct Counter {
    n: Cell<u32>,
}

impl Counter {
    pub fn new() -> Counter {
        Counter { n: Cell::new(0) }
    }

    pub fn incr(&self) {
        self.n.set(self.n.get() + 1);
    }

    pub fn get(&self) -> u32 {
        self.n.get()
    }
}

pub fn two_increments() -> u32 {
    let c = Counter::new();
    c.incr();
    c.incr();
    c.get()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn two_increments_is_2() {
        assert_eq!(two_increments(), 2);
    }
}
