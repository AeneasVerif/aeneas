//@ [!lean] skip
//! Reproducer for https://github.com/AeneasVerif/aeneas/issues/767
//!
//! Passing a tuple-struct constructor as a function pointer (`x.map(Wrapper)`)
//! makes Aeneas synthesize a standalone constructor function whose generated
//! name clashes with the type definition `Wrapper`.
pub struct Wrapper(pub [u8; 32]);

// Broken: `Wrapper` is passed as a first-class function pointer.
pub fn make_wrapper_broken(x: Result<[u8; 32], ()>) -> Result<Wrapper, ()> {
    x.map(Wrapper)
}

// Workaround: wrapping in a closure avoids synthesizing the constructor fn.
pub fn make_wrapper_fixed(x: Result<[u8; 32], ()>) -> Result<Wrapper, ()> {
    x.map(|b| Wrapper(b))
}
