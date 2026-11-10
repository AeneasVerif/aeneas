//! The *consumer* half of the `-emit-json` / `-external-names` round trip: one
//! use of each kind of definition `roundtrip-lib` provides.
//!
//! What the golden asserts is what is *absent*. Translated without
//! `-external-names`, this crate re-declares everything it touches - an
//! `axiom roundtrip_lib.add_one`, a second copy of `structure
//! roundtrip_lib.Counter`, and so on - because the definitions belong to
//! another crate. Translated with the manifest, it imports `RoundtripLib` and
//! calls the real definitions, so none of those declarations appear.

use roundtrip_lib::{
    add_one, id, incr, nested, new_ref, sum_to, Base, Bound, Container, Convert, Counter,
    Describe, Either, Node, Pair, Step, Twice, Wrapper, START,
};

pub fn use_fun(x: u32) -> u32 {
    add_one(x)
}

pub fn use_loop_fun(n: u32) -> u32 {
    sum_to(n)
}

/// `START` is total, so this reads `ok roundtrip.START`. Had the manifest
/// not carried `can_fail: false`, the value would be bound monadically instead.
pub fn use_global() -> u32 {
    START
}

pub fn use_type(c: Counter) -> Counter {
    c
}

/// The variants are named `roundtrip.Bound.Below` and `.Above` here, which is
/// only right because the prefix comes from the manifest rather than from what
/// this crate would have called the type (`roundtrip_lib.Bound`).
pub fn use_enum(b: &Bound) -> u32 {
    match b {
        Bound::Below => 0,
        Bound::Above => 1,
    }
}

/// Resolves through the `trait_impls` bucket, whose entries are registered
/// under the trait applied to the implementation's arguments
/// (`roundtrip_lib::Step<roundtrip_lib::Counter>`) rather than under the
/// implementation's own path.
pub fn use_trait(c: &Counter) -> u32 {
    c.step()
}

/// The three kinds of trait item, reached through a bound rather than through a
/// known implementation: the method, the associated constant, and the parent
/// clause which `Step: Base` introduces.
pub fn use_trait_items<T: Step>(t: &T) -> u32 {
    t.step() + T::STRIDE + t.base()
}

/// A local implementation of a trait the manifest names. The manifest does not
/// list the methods of `Step` (its consumers compute them from the LLBC), so
/// `-filter-trait-methods` must keep them all: the structure generated for the
/// library has every method.
pub struct Local {
    pub v: u32,
}

impl Base for Local {
    fn base(&self) -> u32 {
        self.v
    }
}

impl Step for Local {
    const STRIDE: u32 = 1;

    fn step(&self) -> u32 {
        self.v
    }
}

/// `new_ref` has a backward function, because the lifetime of `MutRef` is used
/// for a mutable borrow: it gives back the new value of `x`.
pub fn use_mut_ref(x: &mut u32) {
    incr(new_ref(x))
}

/// `Node` is recursive, so this calls its constructor, whose name comes from
/// the manifest's `lean_name` (`roundtrip.Node.mk`): the library is
/// translated with `-namespace roundtrip`, while the name this crate would
/// compute is `roundtrip_lib.Node.mk`.
pub fn use_struct_constructor(value: u32) -> Node {
    Node { value, next: None }
}

pub fn base_of<T: Base>(x: &T) -> u32 {
    x.base()
}

/// Each call needs its own implementation of `Base` for `Pair`, as the
/// manifest maps them: the implementation for `q` must not be taken for the
/// generic one, whose pattern would also match it if its variables were
/// anonymous.
pub fn use_pair_impls(p: &Pair<u8, (u32, u32)>, q: &Pair<u8, (u32, u64)>) -> u32 {
    base_of(p) + base_of(q)
}

/// The implementation for `Box<u32>` must be found under its own name, not
/// under the one of the implementation for `Box<dyn Show>`.
pub fn use_box_impl(b: &Box<u32>) -> u32 {
    base_of(b)
}

pub fn use_nested() -> u32 {
    nested::depth()
}

pub fn use_generic_fun(x: u32) -> u32 {
    id(x)
}

pub fn use_generic_enum(e: Either<u32, bool>) -> u32 {
    match e {
        Either::Left(x) => x,
        Either::Right(_) => 0,
    }
}

pub fn use_inherent(c: &Counter) -> u32 {
    c.get() + Counter::ZERO
}

pub fn use_generic_inherent(x: u32) -> Wrapper<u32> {
    Wrapper::new(x)
}

pub fn convert_of<T, C: Convert<T>>(c: &C) -> T {
    c.convert()
}

pub fn use_generic_trait(c: &Counter) -> u64 {
    convert_of(c)
}

pub fn first_of<C: Container<Item = u32>>(c: &C) -> u32 {
    c.first()
}

pub fn use_assoc_type(c: &Counter) -> u32 {
    first_of(c)
}

pub fn code_of<D: Describe>(d: &D) -> u32 {
    d.code()
}

/// The implementation for `Counter` uses the default `code` of the trait,
/// which the library defines.
pub fn use_default_method(c: &Counter) -> u32 {
    code_of(c)
}

pub fn twice_of<T: Twice>(x: &T) -> u32 {
    x.twice()
}

/// The blanket implementation of the library, instantiated at a type of the
/// library and at a type of this crate.
pub fn use_blanket(c: &Counter, l: &Local) -> u32 {
    twice_of(c) + twice_of(l)
}

pub fn use_foreign_self(x: u32) -> u32 {
    base_of(&x)
}

pub fn use_ref_impl(c: &Counter) -> u32 {
    base_of(&c)
}

pub fn use_generic_impl_of_generic_trait(w: &Wrapper<u32>) -> u32 {
    convert_of(w)
}
