//@ [!lean] skip
//! Regression test for the loop fixed-point computation in presence of a
//! shared borrow of an opaque value which itself contains borrows.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Cap {
    pub children: Vec<u32>,
}

/// An opaque guard which (conceptually) borrows a `Cap`. We use an opaque type
/// to avoid relying on interior mutability (e.g. `RefCell`), while still
/// getting a symbolic value whose type contains a nested borrow.
#[verify::opaque]
pub struct Guard<'a> {
    inner: &'a Cap,
}

/// Opaque constructor: borrows a `Cap` and returns a guard.
#[verify::opaque]
pub fn wrap(c: &Cap) -> Guard<'_> {
    unimplemented!()
}

impl<'a> Guard<'a> {
    /// Opaque getter: returns a shared reference to the borrowed `Cap`.
    #[verify::opaque]
    pub fn get(&self) -> &Cap {
        unimplemented!()
    }
}

pub fn carve(cap_ref: &Cap, x: u32) -> bool {
    let parent = wrap(cap_ref);
    for c in &parent.get().children {
        if *c == x {
            return false;
        }
    }
    true
}
