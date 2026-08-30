//@ [!lean] skip
//! Reproducer for https://github.com/AeneasVerif/aeneas/issues/767
//!
//! Using a tuple-struct constructor as a function (`x.map(Wrapper)`) could,
//! if Aeneas uses a naive naming scheme, be assigned a name
//! which clashes with the type definition `Wrapper`.
pub struct Wrapper(pub [u8; 32]);

pub fn make_wrapper(x: Result<[u8; 32], ()>) -> Result<Wrapper, ()> {
    x.map(Wrapper)
}
