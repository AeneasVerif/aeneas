//@ [!lean] skip
//@ [lean] aeneas-args=-rust-source-links
//! Checks the `-rust-source-links` option works
//!
//! We want one declaration of each kind the extraction can produce, and
//! declarations which already carry other attributes.

/// A structure: the only attribute is the one we add.
pub struct Pair {
    pub x: u32,
    pub y: u32,
}

/// An enumeration: merged with `discriminant`.
pub enum Sign {
    Neg,
    Zero,
    Pos,
}

/// A type which extracts to a definition rather than to a structure: merged with
/// `reducible`.
pub struct Empty;

/// A constant, and a static below: global declarations.
pub const ZERO: u32 = 0;

pub static ONE: u32 = 1;

/// A plain function.
pub fn add(x: u32, y: u32) -> u32 {
    x + y
}

/// A function with a loop: the auxiliary declarations generated for the loop carry
/// `rust_loop`/`rust_loop_body`.
pub fn sum_to(n: u32) -> u32 {
    let mut i = 0;
    let mut sum = 0;
    while i < n {
        sum += i;
        i += 1;
    }
    sum
}

/// A recursive function.
pub fn depth(s: &Sign, acc: u32) -> u32 {
    match s {
        Sign::Zero => acc,
        _ => depth(&Sign::Zero, acc + 1),
    }
}

/// Methods of an inherent implementation.
impl Pair {
    pub fn sum(&self) -> u32 {
        self.x + self.y
    }
}

/// A trait declaration, with an associated type, an associated constant and a method.
pub trait Container {
    type Item;
    const NAME: u32;
    fn get(&self) -> Self::Item;
}

/// A trait implementation.
impl Container for Pair {
    type Item = u32;
    const NAME: u32 = 42;
    fn get(&self) -> u32 {
        self.x
    }
}
