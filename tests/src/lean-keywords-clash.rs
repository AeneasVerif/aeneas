//@ [!lean] skip

//! Regression test: a top-level definition named after a Lean keyword is
//! escaped (`«end»`). Generating a unique name for the variable below must
//! take that escaping into account, otherwise the variable is given the very
//! same name as the definition.
//!
//! See `lean-keywords.rs` for the escaping of the names themselves.

pub fn end(x: u32) -> u32 {
    x
}

pub fn clash(end: u32) -> u32 {
    end
}

/// The binders of the projector simp lemmas of a recursive struct are named
/// after the fields, so they are renamed here too - and the body of the
/// lemma must refer to the binder, not to the field.
pub struct Rec {
    pub end: Option<Box<Rec>>,
    pub v: u32,
}
