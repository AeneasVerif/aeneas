//@ [!lean] skip
//! `Iterator::map` and `Map::next` on an arbitrary iterator.

pub fn first_succ(xs: &[u32]) -> Option<u32> {
    xs.iter().map(|x| x + 1).next()
}
