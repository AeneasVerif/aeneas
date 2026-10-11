//@ [!lean] skip
//@ [lean] subdir=OpaqueTraitDecl
//@ [lean] aeneas-args=-split-files
//@ charon-args=--opaque=crate::shapes
//! The declarations of an opaque module, including its trait declarations, are
//! external: with `-split-files`, they are extracted in the templates of the
//! external definitions, and the user provides them (for instance, by importing
//! the model of the crate which defines them).
mod shapes {
    pub trait Shape {
        fn area(&self) -> u32;
    }

    pub struct Circle {
        r: u32,
    }

    pub fn circle(r: u32) -> Circle {
        Circle { r }
    }

    impl Shape for Circle {
        fn area(&self) -> u32 {
            3 * self.r * self.r
        }
    }

    pub fn total<S: Shape>(a: &S, b: &S) -> u32 {
        a.area() + b.area()
    }
}

use shapes::{total, Shape};

pub struct Rect {
    pub w: u32,
    pub h: u32,
}

impl Shape for Rect {
    fn area(&self) -> u32 {
        self.w * self.h
    }
}

pub fn total_rects(a: &Rect, b: &Rect) -> u32 {
    total(a, b)
}

pub fn circle_area(r: u32) -> u32 {
    shapes::circle(r).area()
}
