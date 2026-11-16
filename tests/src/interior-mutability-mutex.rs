//@ [lean] known-failure
//@ [!lean] skip
//! Same as `interior-mutability-cell.rs`, with a mutex: the second `lock(&self)` was merged with
//! the first one, so the write through the first guard was lost.
//!
//! See <https://github.com/AeneasVerif/aeneas/issues/1525>.

use std::sync::Mutex;

pub fn mutex_twice() -> u32 {
    let m = Mutex::new(0u32);
    {
        *m.lock().unwrap() = 5;
    }
    let v = *m.lock().unwrap();
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mutex_twice_is_5() {
        assert_eq!(mutex_twice(), 5);
    }
}
