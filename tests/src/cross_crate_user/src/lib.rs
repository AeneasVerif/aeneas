//! The user crate of the cross-crate translation tests: it implements and uses the traits and
//! items of `cross_crate_lib`. Its translation imports the translation of `cross_crate_lib`.

use cross_crate_lib::{
    bump, helper, sum_double, Circle, Container, Conv, Counter, Dir, HasLen, Msg, Named, Point,
    Shape, Tagged, Wrapper,
};

pub struct Square {
    pub side: u32,
}

/// Only the required method: the defaults of `Shape` come from the library (cases E1, E3, E4, E11).
impl Shape for Square {
    fn area(&self) -> u32 {
        self.side * self.side
    }
}

/// E1: the library's default calls `Square::area`.
pub fn square_double(s: &Square) -> u32 {
    s.double_area()
}

/// E3: a chain of the library's defaults.
pub fn square_quad(s: &Square) -> u32 {
    s.quad_area()
}

/// E4: a default which doesn't use `Self: Shape`.
pub fn square_sides() -> u32 {
    Square::sides()
}

pub struct Rect {
    pub w: u32,
    pub h: u32,
}

/// E2: an impl overriding the default.
impl Shape for Rect {
    fn area(&self) -> u32 {
        self.w * self.h
    }

    fn double_area(&self) -> u32 {
        self.w * self.h * 2
    }
}

pub fn rect_double(r: &Rect) -> u32 {
    r.double_area()
}

/// E5: the library's generic function with this crate's instance.
pub fn two_squares(a: &Square, b: &Square) -> u32 {
    sum_double(a, b)
}

/// E6: the library's generic function with the library's own instance.
pub fn two_circles(a: &Circle, b: &Circle) -> u32 {
    sum_double(a, b)
}

/// E7: a trait with a parent trait.
impl Named for Square {
    fn id(&self) -> u32 {
        self.side
    }
}

impl Tagged for Square {}

pub fn square_tag(s: &Square) -> u32 {
    s.tag()
}

/// E8: a default taking `&mut self`.
pub struct Ticks {
    pub n: u32,
}

impl Counter for Ticks {
    fn incr(&mut self) {
        self.n += 1;
    }
}

pub fn tick_twice(t: &mut Ticks) {
    t.incr_twice()
}

/// E9: an associated constant with a default.
impl HasLen for Square {
    const N: usize = 3;
}

pub fn square_twice_len() -> usize {
    Square::TWICE
}

/// E10: the library's generic impls at this crate's type.
pub fn wrapped_tag(s: Square) -> u32 {
    Wrapper(s).tag()
}

/// E12: a generic trait.
impl Conv<u32> for Square {
    fn conv(&self) -> u32 {
        self.side
    }
}

pub fn square_conv_pair(s: &Square) -> (u32, u32) {
    s.conv_pair()
}

/// E13: this crate's trait, with a default calling the library, implemented for the library's
/// type; and the library's struct and enum.
pub trait Describe {
    fn code(&self) -> u32;

    fn describe(&self) -> u32 {
        self.code() + helper()
    }
}

impl Describe for Circle {
    fn code(&self) -> u32 {
        self.r
    }
}

pub fn circle_describe(c: &Circle) -> u32 {
    c.describe()
}

pub fn point_shift(p: Point) -> Point {
    Point { x: p.x + 1 }
}

pub fn flip(d: Dir) -> Dir {
    match d {
        Dir::L => Dir::R,
        Dir::R => Dir::L,
    }
}

/// E14: a trait with an associated type.
impl Container for Square {
    type Item = u32;

    fn first(&self) -> u32 {
        self.side
    }
}

pub fn square_first_twice(s: &Square) -> (u32, u32) {
    s.first_twice()
}

/// E15: the library's enum with data.
pub fn msg_code(m: Msg) -> u32 {
    match m {
        Msg::Quit => 0,
        Msg::Write(n) => n,
        Msg::Move { x } => x + 1,
    }
}

/// E16: the library's function taking `&mut`.
pub fn grow(c: &mut Circle) {
    bump(c);
    bump(c);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shape_defaults() {
        let s = Square { side: 3 };
        assert_eq!(square_double(&s), 18);
        assert_eq!(square_quad(&s), 36);
        assert_eq!(square_sides(), 4);
        assert_eq!(s.unused_default(), 10);
        assert_eq!(rect_double(&Rect { w: 2, h: 5 }), 20);
    }

    #[test]
    fn generic_functions() {
        assert_eq!(two_squares(&Square { side: 2 }, &Square { side: 3 }), 17);
        assert_eq!(two_circles(&Circle { r: 1 }, &Circle { r: 2 }), 18);
    }

    #[test]
    fn parent_traits_and_generic_impls() {
        assert_eq!(square_tag(&Square { side: 4 }), 5);
        assert_eq!(wrapped_tag(Square { side: 4 }), 105);
    }

    #[test]
    fn mutable_default() {
        let mut t = Ticks { n: 1 };
        tick_twice(&mut t);
        assert_eq!(t.n, 3);
    }

    #[test]
    fn constants_and_generic_traits() {
        assert_eq!(square_twice_len(), 6);
        assert_eq!(square_conv_pair(&Square { side: 7 }), (7, 7));
    }

    #[test]
    fn associated_types_enums_and_mutable_borrows() {
        assert_eq!(square_first_twice(&Square { side: 5 }), (5, 5));
        assert_eq!(msg_code(Msg::Quit), 0);
        assert_eq!(msg_code(Msg::Write(4)), 4);
        assert_eq!(msg_code(Msg::Move { x: 4 }), 5);
        let mut c = Circle { r: 1 };
        grow(&mut c);
        assert_eq!(c.r, 3);
    }

    #[test]
    fn library_items() {
        assert_eq!(circle_describe(&Circle { r: 2 }), 12);
        assert_eq!(point_shift(Point { x: 1 }).x, 2);
        assert!(matches!(flip(Dir::L), Dir::R));
    }
}
