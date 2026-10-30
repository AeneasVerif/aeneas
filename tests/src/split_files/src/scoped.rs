//! Items whose names start with the name of another item. They are in module
//! `scoped`, so they go into `Scoped`, not into modules named after that item.

pub trait Shape {
    // A default method, named `scoped::Shape::sides`.
    fn sides(&self) -> u32 {
        0
    }
}

pub struct Square;

impl Shape for Square {}

pub fn count() -> u32 {
    // Defined in the body of `count`, so named `scoped::count::Local`.
    struct Local {
        v: u32,
    }
    let l = Local { v: Square.sides() };
    l.v
}
