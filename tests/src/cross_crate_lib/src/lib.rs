//! The library crate of the cross-crate translation tests. Its items are used by
//! `cross_crate_user`, which is translated with `-extern-crate cross_crate_lib=...` so that it
//! reuses this crate's Lean translation instead of re-declaring it.

/// A trait whose default methods call the methods that the implementing crate provides.
pub trait Shape {
    fn area(&self) -> u32;

    /// A default method calling a required method (case E1).
    fn double_area(&self) -> u32 {
        2 * self.area()
    }

    /// A default method calling another default method (case E3).
    fn quad_area(&self) -> u32 {
        2 * self.double_area()
    }

    /// A default method which doesn't use `Self: Shape` (case E4).
    fn sides() -> u32 {
        4
    }

    /// A default method that the user crate never calls (case E11).
    fn unused_default(&self) -> u32 {
        self.area() + 1
    }
}

/// A generic function, called by the user crate with its own instance (case E5).
pub fn sum_double<T: Shape>(a: &T, b: &T) -> u32 {
    a.double_area() + b.area()
}

/// A type of this crate with an impl of this crate (case E6).
pub struct Circle {
    pub r: u32,
}

impl Shape for Circle {
    fn area(&self) -> u32 {
        3 * self.r * self.r
    }
}

/// A trait with a parent trait, whose default calls the parent's method (case E7).
pub trait Named {
    fn id(&self) -> u32;
}

pub trait Tagged: Named {
    fn tag(&self) -> u32 {
        self.id() + 1
    }
}

/// A default method taking `&mut self` (case E8).
pub trait Counter {
    fn incr(&mut self);

    fn incr_twice(&mut self) {
        self.incr();
        self.incr();
    }
}

/// An associated constant with a default (case E9).
pub trait HasLen {
    const N: usize;
    const TWICE: usize = 2 * Self::N;
}

/// Generic impls of this crate, used by the user crate at its own types (case E10).
pub struct Wrapper<T>(pub T);

impl<T: Named> Named for Wrapper<T> {
    fn id(&self) -> u32 {
        self.0.id() + 100
    }
}

impl<T: Named> Tagged for Wrapper<T> {}

/// A generic trait (case E12).
pub trait Conv<T> {
    fn conv(&self) -> T;

    fn conv_pair(&self) -> (T, T) {
        (self.conv(), self.conv())
    }
}

/// A function, a struct and an enum used by the user crate (case E13).
pub fn helper() -> u32 {
    10
}

pub struct Point {
    pub x: u32,
}

pub enum Dir {
    L,
    R,
}

/// A trait with an associated type (case E14).
pub trait Container {
    type Item;

    fn first(&self) -> Self::Item;

    fn first_twice(&self) -> (Self::Item, Self::Item) {
        (self.first(), self.first())
    }
}

/// An enum whose variants carry data (case E15).
pub enum Msg {
    Quit,
    Write(u32),
    Move { x: u32 },
}

/// A function taking `&mut` (case E16).
pub fn bump(c: &mut Circle) {
    c.r += 1;
}
