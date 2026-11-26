//@ [!lean] skip
//@ [lean] subdir=EmitJson
//@ [lean] aeneas-args=-emit-json -emit-json-no-version
//! The manifest `translation.json` (`-emit-json`): one item of each kind of entry.

/// A structure: constructor and fields.
pub struct Point {
    pub x: u32,
    pub y: u32,
}

/// A tuple structure: no constructor nor field names.
pub struct Meters(pub u32);

/// An enumeration: variants.
pub enum Dir {
    Left,
    Right(u32),
}

/// A global.
pub const ORIGIN: u32 = 0;

pub trait Named {
    fn id(&self) -> u32;
}

/// A trait with a parent clause, a constant, methods and a default method. Charon makes its
/// associated type a parameter (the impl below is `Shape<Point, u32>`).
pub trait Shape: Named {
    const SIDES: u32;
    type Unit;
    fn area(&self) -> u32;
    fn double_area(&self) -> u32 {
        2 * self.area()
    }
}

impl Named for Point {
    fn id(&self) -> u32 {
        self.x
    }
}

impl Shape for Point {
    const SIDES: u32 = 4;
    type Unit = u32;
    fn area(&self) -> u32 {
        self.x * self.y
    }
}

/// An impl identified by the arguments of the implemented trait.
pub trait Conv<T> {
    fn conv(&self) -> T;
}

impl Conv<u64> for Point {
    fn conv(&self) -> u64 {
        self.x as u64
    }
}

pub fn double_area_of(p: &Point) -> u32 {
    p.double_area()
}
