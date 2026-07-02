//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/801

trait T<X> {
    fn dummy() -> X;
}

fn test<P: for<'a> T<&'a u8>>() -> u8 {
    *P::dummy()
}
