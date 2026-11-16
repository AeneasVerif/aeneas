//@ [!lean] skip
//@ [lean] subdir=ThreadSpawn
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `thread::spawn` and `JoinHandle::join`.
//!
//! The model runs a closure to completion when its thread is spawned, which is sound if the threads
//! only read immutable data and write data they own (the functions below).
//! `computation` is the example of the documentation of `thread::spawn`
//! (<https://doc.rust-lang.org/std/thread/fn.spawn.html>).

use std::thread;

pub fn computation() -> u32 {
    let computation = thread::spawn(|| {
        // Some expensive computation.
        42
    });
    let result = computation.join().unwrap();
    result
}

#[verify::test]
pub fn test_computation() {
    assert!(computation() == 42);
}

/// The closure moves its environment into the thread.
pub fn moved(x: u32, y: u32) -> u32 {
    let handle = thread::spawn(move || x + y);
    handle.join().unwrap()
}

#[verify::test]
pub fn test_moved() {
    assert!(moved(1, 2) == 3);
}

fn double(x: u32) -> u32 {
    x * 2
}

/// Two independent threads, joined in the opposite order.
pub fn fork_join(x: u32, y: u32) -> u32 {
    let h1 = thread::spawn(move || double(x));
    let h2 = thread::spawn(move || double(y));
    let b = h2.join().unwrap();
    let a = h1.join().unwrap();
    a + b
}

#[verify::test]
pub fn test_fork_join() {
    assert!(fork_join(3, 4) == 14);
}

/// A thread which takes a vector, modifies it and returns it.
pub fn fill(mut v: Vec<u32>) -> Vec<u32> {
    let handle = thread::spawn(move || {
        v.push(7);
        v
    });
    handle.join().unwrap()
}

#[verify::test]
pub fn test_fill() {
    let v = fill(Vec::new());
    assert!(v.len() == 1);
    assert!(v[0] == 7);
}

/// The result of `join` can be matched.
pub fn join_match(x: u32) -> u32 {
    let handle = thread::spawn(move || x + 1);
    match handle.join() {
        Ok(v) => v,
        Err(_) => 0,
    }
}

#[verify::test]
pub fn test_join_match() {
    assert!(join_match(5) == 6);
}

/// A panic in the thread is a failure of the whole computation.
pub fn overflow(x: u32) -> u32 {
    let handle = thread::spawn(move || x + 1);
    handle.join().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn thread_spawn() {
        test_computation();
        test_moved();
        test_fork_join();
        test_fill();
        test_join_match();
        assert!(overflow(1) == 2);
    }
}
