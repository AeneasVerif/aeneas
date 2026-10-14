//@ [!lean] skip
//@ [lean] aeneas-args=-gen-layouts

pub struct UnitStruct;

pub struct Newtype(pub u32);

pub struct Point {
    pub x: i32,
    pub y: u64,
}

pub struct Pair(pub u8, pub bool);

pub struct Triple(pub u8, pub u16, pub bool);

pub struct Wrapper<T1, T2> {
    pub first: T1,
    pub second: T2,
}

pub enum Color {
    Red,
    Green,
    Blue,
}

pub enum Shape {
    Empty,
    Circle(u32),
    Rect { width: usize, height: usize },
}

pub enum Bazinga<T1, T2, T3> {
    Foo1,
    Foo2 { x: usize, y: T1 },
    Foo3(T2, T3),
    Foo4(bool),
}

pub struct Scene {
    pub bg: Color,
    pub main_shape: Shape,
}

#[repr(C)]
pub enum Repr1 {
    Empty,
    Circle(u32),
    Rect { width: usize, height: usize },
}

#[repr(C, i8)]
pub enum Repr2 {
    Empty,
    Circle(u32),
    Rect { width: usize, height: usize },
}

#[repr(i8)]
pub enum Repr3 {
    Empty,
    Circle(u32),
    Rect { width: usize, height: usize },
}

fn main() {
    let x1 = Repr1::Empty;
    let x1 = Repr2::Empty;
    let x1 = Repr3::Empty;
}
