//@ [!lean] skip
use std::convert::TryInto;

fn slice_to_array(s: &[u8]) -> &[u8; 32] {
    s.try_into().unwrap()
}

fn slice_to_array1(s: &[u8]) -> &[u8; 32] {
    s.try_into().expect("Expected a slice of length 32")
}
