//! The *provider* half of the `-emit-json` / `-external-names` round trip.
//!
//! This crate is translated with `-emit-json`, which writes
//! `tests/lean/RoundtripLib/translation.json` next to the Lean it generates.
//! `roundtrip-user` is then translated with that file passed to
//! `-external-names`, so its calls into this crate land on the names below
//! instead of on axioms of its own.
//!
//! One definition of each kind the manifest has a bucket for. The crate is
//! translated with `-namespace roundtrip`, so the names the manifest gives
//! differ from those a consumer would compute from the Rust paths.

pub struct Counter {
    pub value: u32,
}

/// The manifest names the type but not its variants: a consumer recomputes
/// those from the LLBC, prefixed with the name the manifest gives.
pub enum Bound {
    Below,
    Above,
}

/// A total global: extracted as `U32`, not as `Result U32`. The manifest says
/// so through `can_fail`; a consumer which missed it would bind it as a
/// `Result` (`let i ← roundtrip.START`), which does not typecheck.
pub const START: u32 = 7;

pub trait Base {
    fn base(&self) -> u32;
}

/// A parent clause, an associated constant and a method, which the manifest
/// does not name: a consumer computes them from the LLBC, on the trait's name.
pub trait Step: Base {
    const STRIDE: u32;

    fn step(&self) -> u32;
}

impl Base for Counter {
    fn base(&self) -> u32 {
        self.value
    }
}

impl Step for Counter {
    const STRIDE: u32 = 2;

    fn step(&self) -> u32 {
        self.value
    }
}

pub fn add_one(x: u32) -> u32 {
    x + 1
}

/// Extracted as three Lean declarations - the function, the loop and its body -
/// which the manifest reports as three `functions` rows sharing this name. The
/// two loop rows carry a `loop` key, and a reader which registered them would
/// map `sum_to` to a declaration of a different arity.
pub fn sum_to(n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += i;
        i += 1;
    }
    s
}

/// Its lifetime is used for a mutable borrow, which the manifest does not say:
/// a consumer, to which the type is opaque, gets it from Charon's analysis.
pub struct MutRef<'a> {
    x: &'a mut u32,
}

pub fn new_ref(x: &mut u32) -> MutRef<'_> {
    MutRef { x }
}

pub fn incr(m: MutRef<'_>) {
    *m.x += 1;
}

/// A name the pattern syntax cannot spell (Charon prints no character literal
/// in a pattern): the manifest row of `tag` has no `rust_pattern`, with a
/// warning, instead of the whole translation stopping.
pub struct Tagged<const C: char>;

impl Tagged<'a'> {
    pub fn tag() -> u32 {
        0
    }
}

/// Recursive, so a consumer builds it with its constructor rather than with a
/// structure update; the manifest has no `body` for it, and the constructor
/// is named after its `lean_name` (`roundtrip.Node.mk`), not after the
/// Rust path.
pub struct Node {
    pub value: u32,
    pub next: Option<Box<Node>>,
}

pub struct Pair<A, B> {
    pub a: A,
    pub b: B,
}

/// Two implementations of one trait which only differ by their arguments:
/// the manifest names their variables after the parameters of the
/// implementation (`Base<Pair<@A, (@B, @B)>>`), so the pattern of the first
/// does not also match the second, whose `(u32, u64)` is concrete.
impl<A, B> Base for Pair<A, (B, B)> {
    fn base(&self) -> u32 {
        1
    }
}

impl<A> Base for Pair<A, (u32, u64)> {
    fn base(&self) -> u32 {
        2
    }
}

pub trait Show {}

/// A name involving a type the pattern syntax cannot spell: `dyn Show` would
/// print as the anonymous `@`, and `Base<Box<@>>` would also match the next
/// implementation. The manifest gives this one no `rust_pattern`, with a
/// warning.
impl Base for Box<dyn Show> {
    fn base(&self) -> u32 {
        3
    }
}

impl Base for Box<u32> {
    fn base(&self) -> u32 {
        4
    }
}

/// A definition under a module: the manifest gives its full path.
pub mod nested {
    pub fn depth() -> u32 {
        1
    }
}

/// A generic function.
pub fn id<T>(x: T) -> T {
    x
}

/// A generic enumeration whose variants have fields.
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// An inherent implementation: a method and an associated constant, whose
/// patterns are under the type (`roundtrip_lib::{roundtrip_lib::Counter}::get`).
impl Counter {
    pub const ZERO: u32 = 0;

    pub fn get(&self) -> u32 {
        self.value
    }
}

pub struct Wrapper<T> {
    pub inner: T,
}

/// A generic inherent implementation
/// (`roundtrip_lib::{roundtrip_lib::Wrapper<@T>}::new`).
impl<T> Wrapper<T> {
    pub fn new(inner: T) -> Self {
        Wrapper { inner }
    }
}

/// A trait with a type parameter: its implementation is registered under
/// `Convert<Counter, u64>`, `Self` first.
pub trait Convert<T> {
    fn convert(&self) -> T;
}

impl Convert<u64> for Counter {
    fn convert(&self) -> u64 {
        self.value as u64
    }
}

/// A trait with an associated type.
pub trait Container {
    type Item;

    fn first(&self) -> Self::Item;
}

impl Container for Counter {
    type Item = u32;

    fn first(&self) -> u32 {
        self.value
    }
}

/// A method with a default implementation, which the implementation below
/// does not override.
pub trait Describe {
    fn code(&self) -> u32 {
        0
    }
}

impl Describe for Counter {}

/// A blanket implementation, registered under `Twice<@T>`: it applies to any
/// type which implements `Base`, including the types of the consumer.
pub trait Twice {
    fn twice(&self) -> u32;
}

impl<T: Base> Twice for T {
    fn twice(&self) -> u32 {
        self.base()
    }
}

/// An implementation for a type of another crate.
impl Base for u32 {
    fn base(&self) -> u32 {
        *self
    }
}

/// An implementation for a reference, whose pattern has a region.
impl<'a> Base for &'a Counter {
    fn base(&self) -> u32 {
        self.value
    }
}

/// A generic implementation of a trait with a type parameter
/// (`Convert<Wrapper<@T>, @T>`).
impl<T: Copy> Convert<T> for Wrapper<T> {
    fn convert(&self) -> T {
        self.inner
    }
}
