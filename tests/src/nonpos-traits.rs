//@ [!lean] skip
//! Traits that break positivity: a method takes another implementor of the same trait.
//! In Lean, such a trait can't be an ordinary `structure`, so Aeneas emits a `nonpos_structure`.

pub trait Bla {
    fn to_num(&self) -> u32;
    fn add<Other: Bla>(&self, other: &Other) -> u32;
}

impl Bla for u32 {
    fn to_num(&self) -> u32 {
        *self
    }
    fn add<Other: Bla>(&self, other: &Other) -> u32 {
        *self + other.to_num()
    }
}

pub fn use_bla() -> u32 {
    3u32.add(&4u32)
}

// An impl which refers to itself: `bigger` is a provided method, so the impl of `Sized2` for
// `u32` uses its default, which takes the impl itself as an argument.
// TODO: not supported yet; Aeneas prints the impl with `impl_def`, which doesn't work for a
// `nonpos_structure` (it should use `partial_fixpoint`).
pub trait Sized2 {
    fn area(&self) -> u32;
    fn bigger<Other: Sized2>(&self, other: &Other) -> bool {
        self.area() > other.area()
    }
    // A provided method with no generics: the impl's field is `Sized2.double.default X`, without
    // a lambda, so evaluating `X` evaluates `X` again. TODO: the field must be eta-expanded
    // (`fun x => Sized2.double.default X x`), otherwise the code type-checks but loops when run.
    fn double(&self) -> u32 {
        self.area() + self.area()
    }
}

impl Sized2 for u32 {
    fn area(&self) -> u32 {
        *self
    }
}

pub fn use_sized2() -> bool {
    3u32.bigger(&4u32)
}

pub fn use_double() -> u32 {
    3u32.double()
}

// A group of mutually recursive traits: neither trait refers to itself, but each one refers to
// the other.
// TODO: not supported yet; Aeneas prints them as ordinary structures, one after the other.
pub trait Left {
    fn val(&self) -> u32;
    fn via_right<R: Right>(&self, r: &R) -> u32;
}

pub trait Right {
    fn via_left<L: Left>(&self, l: &L) -> u32;
}

impl Left for u32 {
    fn val(&self) -> u32 {
        *self
    }
    fn via_right<R: Right>(&self, r: &R) -> u32 {
        r.via_left(self)
    }
}

impl Right for u32 {
    fn via_left<L: Left>(&self, l: &L) -> u32 {
        l.val()
    }
}

pub fn use_left_right() -> u32 {
    3u32.via_right(&4u32)
}
