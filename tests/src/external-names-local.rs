//@ [lean] known-failure
//@ [!lean] skip
//@ [lean] aeneas-args=-external-names tests/external-names/external-names-local.json
//! Checks that mapping a definition of *this* crate to a model is an error: `f`
//! has a body, so the entry in the JSON file would silently replace it.
//!
//! The opaque case is the legitimate one, and is what `external-names.rs`
//! covers.

fn f(x: u32) -> u32 {
    x
}
