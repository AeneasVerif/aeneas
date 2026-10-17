//@ [!lean] skip
//! `<[T]>::split_first_chunk`, as used by rustc-hash.

pub fn first_two(s: &[u8]) -> u8 {
    match s.split_first_chunk::<2>() {
        Some((chunk, _rest)) => chunk[0] ^ chunk[1],
        None => 0,
    }
}
