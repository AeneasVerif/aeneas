//@ [!lean] skip
use std::convert::TryInto;

fn slice_to_array(s : &[u8]) -> &[u8; 32] {
    s.try_into().unwrap()
}
