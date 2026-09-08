//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/1207
// Charon issue: https://github.com/AeneasVerif/charon/issues/1040
//
// Charon leaves closure lifetime arguments erased in function signatures.
// The prepass repairs them when the signature has exactly one possible region.

pub struct Holder<F>(F);

/// Return a closure directly.
pub fn make<'a>(x: &'a u8) -> impl Fn() -> u8 + 'a {
    move || *x
}

/// Return a closure nested inside an iterator adapter.
pub fn iter_of(x: &u8) -> impl Iterator<Item = u8> + '_ {
    (0..1).map(move |_| *x)
}

/// Call a function whose output signature contains the affected closure.
pub fn consume(x: &u8) -> u8 {
    let mut it = iter_of(x);
    match it.next() {
        Some(b) => b,
        None => 0,
    }
}

/// Return a closure nested inside a user-defined type.
pub fn nested(x: &u8) -> Holder<impl Fn() -> u8 + '_> {
    Holder(move || *x)
}
