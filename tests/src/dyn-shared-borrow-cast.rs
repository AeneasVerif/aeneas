//@ [!lean] skip
//@ [lean] known-failure
// Coercing a shared borrow to `&dyn Trait`: Charon emits the unsizing cast
// followed by an identity upcast of the (reborrowed) `&dyn Trait`.
pub trait Shape {
    fn area(&self) -> u32;
}

impl Shape for u32 {
    fn area(&self) -> u32 {
        *self
    }
}

pub fn as_dyn(x: &u32) -> &dyn Shape {
    x
}
