//@ [!lean] skip
//@ [lean] subdir=Arc
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean model of `Arc` (<https://doc.rust-lang.org/std/sync/struct.Arc.html>).
//!
//! `new_five`, `clone_five` and `from_x` adapt the examples of the documentation of `Arc::new`,
//! `Clone::clone` and `From<T>`. The reference counts and the identity of the allocation are not
//! modelled, so the tests only look at the content.

use std::borrow::Borrow;
use std::sync::Arc;

/// Example of `Arc::new`.
pub fn new_five() -> u32 {
    let five = Arc::new(5u32);
    *five
}

#[verify::test]
pub fn test_new_five() {
    assert!(new_five() == 5);
}

/// Example of `Clone::clone`: the clone has the same content as the original.
pub fn clone_five() -> (u32, u32) {
    let five = Arc::new(5u32);
    let same = Arc::clone(&five);
    (*five, *same)
}

#[verify::test]
pub fn test_clone_five() {
    let (a, b) = clone_five();
    assert!(a == 5);
    assert!(b == 5);
}

/// Example of `From<T>`.
pub fn from_x(x: u32) -> bool {
    let arc = Arc::new(x);
    let from: Arc<u32> = Arc::from(x);
    *from == *arc
}

#[verify::test]
pub fn test_from_x() {
    assert!(from_x(5));
    assert!(from_x(0));
}

/// `AsRef` and `Borrow` give access to the content.
pub fn as_ref_and_borrow(x: u32) -> (u32, u32) {
    let arc = Arc::new(x);
    let r: &u32 = arc.as_ref();
    let b: &u32 = Borrow::borrow(&arc);
    (*r, *b)
}

#[verify::test]
pub fn test_as_ref_and_borrow() {
    let (a, b) = as_ref_and_borrow(7);
    assert!(a == 7);
    assert!(b == 7);
}

pub struct Config {
    pub scale: u32,
    pub offset: u32,
}

pub fn apply(cfg: &Arc<Config>, x: u32) -> u32 {
    x * cfg.scale + cfg.offset
}

/// Two handles to the same immutable data.
pub fn share(cfg: Arc<Config>, x: u32, y: u32) -> (u32, u32) {
    let other = Arc::clone(&cfg);
    (apply(&cfg, x), apply(&other, y))
}

#[verify::test]
pub fn test_share() {
    let cfg = Arc::new(Config {
        scale: 3,
        offset: 1,
    });
    let (a, b) = share(cfg, 2, 5);
    assert!(a == 7);
    assert!(b == 16);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arc() {
        test_new_five();
        test_clone_five();
        test_from_x();
        test_as_ref_and_borrow();
        test_share();
    }
}
