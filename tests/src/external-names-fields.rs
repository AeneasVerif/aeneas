//@ [!lean] skip
//@ charon-args=--opaque=external_names_fields::tag --opaque=external_names_fields::first --opaque=external_names_fields::LIMIT --opaque=external_names_fields::Tagged
//@ [lean] aeneas-args=-filter-trait-methods -external-names tests/external-names/external-names-fields.json -extra-includes=ExternalNamesModel
//! The optional fields of a list of external names written by hand, which map
//! the definitions below (opaque ones of this crate, and some of `core`) to
//! the models of `tests/lean/ExternalNamesModel.lean`.

use core::fmt::Write;
use core::ops::RangeToInclusive;
use core::task::Poll;

/// `keep_params: [false]`, `can_fail: false` and `lift: false`: the model takes
/// no type and is used as a value.
pub fn tag<T>() -> u32 {
    0
}

/// `keep_trait_clauses: [false]`: the model takes no `Clone` instance.
pub fn first<T: Clone>(x: &T) -> T {
    x.clone()
}

/// A `globals` entry with `can_fail: false`.
pub const LIMIT: u32 = 10;

/// `keep_params: [true, false]`: the model only takes `T`.
pub struct Tagged<T, U>(T, U);

pub fn use_tag() -> u32 {
    tag::<bool>()
}

pub fn use_first(x: &u32) -> u32 {
    first(x)
}

pub fn use_limit() -> u32 {
    LIMIT
}

pub fn use_tagged(t: Tagged<u32, bool>) -> Tagged<u32, bool> {
    t
}

/// A structure of `core` whose `body` renames its field (`end` is `hi`).
pub fn use_range(r: RangeToInclusive<u32>) -> u32 {
    r.end
}

/// An enumeration of `core` whose `body` gives the full names of its variants
/// (`prefix_variant_names: false`).
pub fn use_poll(p: Poll<u32>) -> u32 {
    match p {
        Poll::Ready(x) => x,
        Poll::Pending => 0,
    }
}

pub fn dup<U: Clone>(u: &U) -> U {
    u.clone()
}

/// A `trait_impls` entry, for the implementation of `Clone` for `Poll`.
pub fn use_poll_clone(p: &Poll<u32>) -> Poll<u32> {
    dup(p)
}

pub struct Counter {
    pub n: usize,
}

/// The trait entry lists `write_char` with `has_default: true`: this
/// implementation keeps the default, which the model library defines.
impl Write for Counter {
    fn write_str(&mut self, _s: &str) -> core::fmt::Result {
        self.n = self.n.wrapping_add(1);
        Ok(())
    }
}

pub fn use_write_char(c: &mut Counter) -> core::fmt::Result {
    c.write_char('x')
}
