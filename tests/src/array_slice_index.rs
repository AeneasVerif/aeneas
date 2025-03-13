//@ [!lean] skip
//! Exercise the translation of the Index trait
use std::ops::*;

pub fn slice_use_index_range_from(s: &[u32]) -> &[u32] {
    s.index(RangeFrom { start: 0 })
}

pub fn slice_use_get_range_from(s: &[u32]) -> Option<&[u32]> {
    s.get(RangeFrom { start: 0 })
}

pub fn slice_use_index_range(s: &[u32]) -> &[u32] {
    s.index(Range { start: 0, end: 1 })
}

pub fn slice_use_get_range(s: &[u32]) -> Option<&[u32]> {
    s.get(Range { start: 0, end: 1 })
}

pub fn slice_use_index_mut_range_from(s: &mut [u32]) -> &mut [u32] {
    s.index_mut(RangeFrom { start: 0 })
}

pub fn slice_use_get_mut_range_from(s: &mut [u32]) -> Option<&mut [u32]> {
    s.get_mut(RangeFrom { start: 0 })
}
