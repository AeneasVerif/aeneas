//@ [!lean] skip
//@ [lean] subdir=ThreadScope
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `thread::scope`, `Scope::spawn` and `ScopedJoinHandle::join`.
//!
//! Scoped threads borrow local data, as in the example of the documentation of `thread::scope`
//! (<https://doc.rust-lang.org/std/thread/fn.scope.html>). The model runs a thread to completion
//! when it is spawned, which is sound if the threads only read shared immutable data and write
//! data they own: the threads below only read `a`. (A scoped thread which writes through a `&mut`
//! borrow of the environment is not supported yet: the instances of `FnOnce` of the closures which
//! hold a `&mut` don't typecheck, see the issues about generic types instantiated with mutable
//! borrows.)

use std::thread;

/// Two threads borrow `a`; they are joined in the opposite order than they were spawned.
pub fn first_two(a: &[u32]) -> u32 {
    thread::scope(|s| {
        let h1 = s.spawn(|| a[0]);
        let h2 = s.spawn(|| a[1]);
        let y = h2.join().unwrap();
        let x = h1.join().unwrap();
        x + y
    })
}

#[verify::test]
pub fn test_first_two() {
    let a = [1u32, 2, 3];
    assert!(first_two(&a) == 3);
}

/// A scoped thread which is not joined still runs to completion before `scope` returns: a panic in
/// it (here an out-of-bounds access) is a panic of `scope`.
pub fn not_joined(a: &[u32]) -> u32 {
    thread::scope(|s| {
        s.spawn(|| a[0]);
        5
    })
}

#[verify::test]
pub fn test_not_joined() {
    let a = [1u32, 2, 3];
    assert!(not_joined(&a) == 5);
}

/// The result of the closure of `scope` is the result of `scope`.
pub fn borrowed_len(a: &[u32]) -> usize {
    thread::scope(|s| {
        let h = s.spawn(|| a.len());
        h.join().unwrap()
    })
}

#[verify::test]
pub fn test_borrowed_len() {
    let a = [1u32, 2, 3];
    assert!(borrowed_len(&a) == 3);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn thread_scope() {
        test_first_two();
        test_not_joined();
        test_borrowed_len();
    }
}
