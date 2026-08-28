//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/1207
// Charon issue: https://github.com/AeneasVerif/charon/issues/1040
//
// Charon leaves the lifetime arguments of closure types erased when a closure appears in a function
// signature, so all of the functions below used to fail with an internal error. The
// `fix_closure_signature_regions` prepass fills them in when the signature binds exactly one region
// parameter, which is forced.
//

pub struct Holder<F>(F);

/// Returning the closure directly.
pub fn make<'a>(x: &'a u8) -> impl Fn() -> u8 + 'a {
    move || *x
}

/// The closure nested inside an iterator adapter: the shape of
/// `Scalar::bits_le` in curve25519-dalek.
pub fn iter_of(x: &u8) -> impl Iterator<Item = u8> + '_ {
    (0..1).map(move |_| *x)
}

/// A caller of the above. This used to fail separately, at a different
/// assertion, because the erased region reached `mk_fresh_symbolic_value`.
pub fn consume(x: &u8) -> u8 {
    let mut it = iter_of(x);
    match it.next() {
        Some(b) => b,
        None => 0,
    }
}

/// The closure below a user type rather than directly in the return type.
pub fn nested(x: &u8) -> Holder<impl Fn() -> u8 + '_> {
    Holder(move || *x)
}
