//@ [!lean] skip

//! Regression test: `end` is a Lean keyword, but a perfectly legal Rust
//! identifier. Such names must be escaped with French quotes (`«end»`)
//! when they are used as a Lean identifier.
//!
//! See `lean-keywords-clash.rs` for the case where the crate also defines an
//! item named after a keyword.

pub struct Struct {
    pub start: u32,
    pub end: u32,
}

pub enum Enum {
    Variant { end: u32 },
    Other(u32),
}

/// A variant named after a keyword. The variant declaration prints the name on
/// its own, so it must be escaped; the uses are qualified (`Keyword.end`) and
/// must *not* be escaped.
#[allow(non_camel_case_types)]
pub enum Keyword {
    end(u32),
    Other(u32),
}

/// The binder and the occurrence must agree.
pub fn parameter(end: u32) -> u32 {
    end
}

/// Same for a binder introduced by a pattern.
pub fn pattern(e: Enum) -> u32 {
    match e {
        Enum::Variant { end } => end,
        Enum::Other(other) => other,
    }
}

/// Building and matching on a variant named after a keyword.
pub fn variant(k: Keyword) -> u32 {
    match k {
        Keyword::end(x) => x,
        Keyword::Other(x) => x,
    }
}

pub fn make_variant(x: u32) -> Keyword {
    Keyword::end(x)
}

/// Same for a type variable.
#[allow(non_camel_case_types)]
pub fn type_variable<end>(x: end) -> end {
    x
}

pub fn field(s: Struct) -> u32 {
    s.end
}

impl Struct {
    pub fn end(&self) -> u32 {
        self.start
    }
}

/// A recursive struct is extracted as an inductive plus projector simp
/// lemmas, whose binders are named after the fields.
pub struct Rec {
    pub end: Option<Box<Rec>>,
    pub v: u32,
}
