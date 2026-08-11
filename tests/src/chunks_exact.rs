//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for chunks_exact iterator, verifying the model matches Rust behavior.

/// chunks_exact(3) on a 6-element array (exact fit): 2 full chunks, empty remainder
#[verify::test]
pub fn test_chunks_exact_exact_fit() {
    let v: [u32; 6] = [1, 2, 3, 4, 5, 6];
    let mut it = v.chunks_exact(3);
    let c1 = it.next().unwrap();
    assert!(c1[0] == 1);
    assert!(c1[1] == 2);
    assert!(c1[2] == 3);
    let c2 = it.next().unwrap();
    assert!(c2[0] == 4);
    assert!(c2[1] == 5);
    assert!(c2[2] == 6);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 0);
}

/// chunks_exact(3) on a 7-element array: 2 chunks, remainder [7]
#[verify::test]
pub fn test_chunks_exact_with_remainder() {
    let v: [u32; 7] = [1, 2, 3, 4, 5, 6, 7];
    let mut it = v.chunks_exact(3);
    let c1 = it.next().unwrap();
    assert!(c1[0] == 1);
    assert!(c1[1] == 2);
    assert!(c1[2] == 3);
    let c2 = it.next().unwrap();
    assert!(c2[0] == 4);
    assert!(c2[1] == 5);
    assert!(c2[2] == 6);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 1);
    assert!(rem[0] == 7);
}

/// chunks_exact(3) on a 5-element array: 1 chunk, remainder [40, 50]
#[verify::test]
pub fn test_chunks_exact_remainder_2() {
    let v: [u32; 5] = [10, 20, 30, 40, 50];
    let mut it = v.chunks_exact(3);
    let c = it.next().unwrap();
    assert!(c[0] == 10);
    assert!(c[1] == 20);
    assert!(c[2] == 30);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 2);
    assert!(rem[0] == 40);
    assert!(rem[1] == 50);
}

/// chunks_exact(1) gives each element as a chunk, no remainder
#[verify::test]
pub fn test_chunks_exact_size_1() {
    let v: [u32; 3] = [10, 20, 30];
    let mut it = v.chunks_exact(1);
    let c1 = it.next().unwrap();
    assert!(c1[0] == 10);
    let c2 = it.next().unwrap();
    assert!(c2[0] == 20);
    let c3 = it.next().unwrap();
    assert!(c3[0] == 30);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 0);
}

/// chunks_exact on an empty slice: no chunks, empty remainder
#[verify::test]
pub fn test_chunks_exact_empty() {
    let v: [u32; 0] = [];
    let mut it = v.chunks_exact(3);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 0);
}

/// chunks_exact with chunk_size > slice length: no chunks, all elements are remainder
#[verify::test]
pub fn test_chunks_exact_chunk_larger_than_slice() {
    let v: [u32; 2] = [1, 2];
    let mut it = v.chunks_exact(5);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 2);
    assert!(rem[0] == 1);
    assert!(rem[1] == 2);
}

/// chunks_exact with chunk_size = slice length: 1 chunk, empty remainder
#[verify::test]
pub fn test_chunks_exact_chunk_equals_slice() {
    let v: [u32; 3] = [1, 2, 3];
    let mut it = v.chunks_exact(3);
    let c = it.next().unwrap();
    assert!(c[0] == 1);
    assert!(c[1] == 2);
    assert!(c[2] == 3);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 0);
}

/// chunks_exact(2) on an odd-length slice: remainder [5]
#[verify::test]
pub fn test_chunks_exact_2_odd() {
    let v: [u32; 5] = [1, 2, 3, 4, 5];
    let mut it = v.chunks_exact(2);
    let c1 = it.next().unwrap();
    assert!(c1[0] == 1);
    assert!(c1[1] == 2);
    let c2 = it.next().unwrap();
    assert!(c2[0] == 3);
    assert!(c2[1] == 4);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 1);
    assert!(rem[0] == 5);
}

/// chunks_exact(2) on a 1-element slice: no chunks, remainder [42]
#[verify::test]
pub fn test_chunks_exact_2_single_element() {
    let v: [u32; 1] = [42];
    let mut it = v.chunks_exact(2);
    assert!(it.next().is_none());
    let rem = it.remainder();
    assert!(rem.len() == 1);
    assert!(rem[0] == 42);
}
