//@ [lean] known-failure
//@ [!lean] skip
//@ [lean] aeneas-args=-external-names tests/external-names/external-names-local-impl.json
//! Checks that mapping a trait impl of *this* crate to a model is an error. A
//! trait impl cannot be made opaque, so the message must not suggest it.

pub trait Tr {
    fn m(&self) -> u32;
}

impl Tr for u32 {
    fn m(&self) -> u32 {
        *self
    }
}
