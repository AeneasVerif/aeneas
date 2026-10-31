//@ [!lean] skip
//! `Iterator::chain` and `Chain::next`.

pub fn first<'a>(xs: &'a [u32], ys: &'a [u32]) -> Option<&'a u32> {
    xs.iter().chain(ys.iter()).next()
}
