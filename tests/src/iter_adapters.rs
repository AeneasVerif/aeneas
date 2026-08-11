//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

//! Tests for iterator adapters: enumerate, take, and range iteration
//! over various scalar types.

// ============================================================================
// Enumerate tests
// ============================================================================

/// Enumerate on a slice yields (index, element) pairs
#[verify::test]
pub fn test_enumerate_slice() {
    let v: [u32; 3] = [10, 20, 30];
    let mut it = v.iter().enumerate();
    let (i0, x0) = it.next().unwrap();
    assert!(i0 == 0 && *x0 == 10);
    let (i1, x1) = it.next().unwrap();
    assert!(i1 == 1 && *x1 == 20);
    let (i2, x2) = it.next().unwrap();
    assert!(i2 == 2 && *x2 == 30);
    assert!(it.next().is_none());
}

/// Enumerate on empty slice returns nothing
#[verify::test]
pub fn test_enumerate_empty() {
    let v: [u32; 0] = [];
    let mut it = v.iter().enumerate();
    assert!(it.next().is_none());
}

// ============================================================================
// Take tests
// ============================================================================

/// Take(2) on a 4-element slice yields first 2
#[verify::test]
pub fn test_take_2() {
    let v: [u32; 4] = [10, 20, 30, 40];
    let mut it = v.iter().take(2);
    assert!(*it.next().unwrap() == 10);
    assert!(*it.next().unwrap() == 20);
    assert!(it.next().is_none());
}

/// Take(0) yields nothing
#[verify::test]
pub fn test_take_0() {
    let v: [u32; 3] = [10, 20, 30];
    let mut it = v.iter().take(0);
    assert!(it.next().is_none());
}

/// Take more than available yields all elements
#[verify::test]
pub fn test_take_more_than_available() {
    let v: [u32; 3] = [1, 2, 3];
    let mut it = v.iter().take(5);
    assert!(*it.next().unwrap() == 1);
    assert!(*it.next().unwrap() == 2);
    assert!(*it.next().unwrap() == 3);
    assert!(it.next().is_none());
}

// ============================================================================
// Range iteration over various scalar types
// ============================================================================

/// Range over u8
#[verify::test]
pub fn test_range_u8() {
    let mut count: u32 = 0;
    for _i in 0u8..5u8 {
        count = count + 1;
    }
    assert!(count == 5);
}

/// Range over u16
#[verify::test]
pub fn test_range_u16() {
    let mut count: u32 = 0;
    for _i in 0u16..4u16 {
        count = count + 1;
    }
    assert!(count == 4);
}

/// Range over u32
#[verify::test]
pub fn test_range_u32() {
    let mut count: u32 = 0;
    for _i in 0u32..3u32 {
        count = count + 1;
    }
    assert!(count == 3);
}

/// Range over u64
#[verify::test]
pub fn test_range_u64() {
    let mut count: u64 = 0;
    for _i in 0u64..4u64 {
        count = count + 1;
    }
    assert!(count == 4);
}

/// Range over usize
#[verify::test]
pub fn test_range_usize() {
    let mut count: usize = 0;
    for _i in 0usize..5usize {
        count = count + 1;
    }
    assert!(count == 5);
}

/// Empty range yields nothing
#[verify::test]
pub fn test_range_empty() {
    let mut count: u32 = 0;
    for _i in 5u8..5u8 {
        count = count + 1;
    }
    assert!(count == 0);
}

// ============================================================================
// IntoIterator for shared array and slice references
// ============================================================================

/// IntoIterator for &[T; N]
#[verify::test]
pub fn test_array_into_iter() {
    let arr: [u32; 3] = [10, 20, 30];
    let mut it = arr.iter();
    assert!(*it.next().unwrap() == 10);
    assert!(*it.next().unwrap() == 20);
    assert!(*it.next().unwrap() == 30);
    assert!(it.next().is_none());
}

/// IntoIterator for &[T] (via slice)
#[verify::test]
pub fn test_slice_into_iter() {
    let arr: [u32; 4] = [1, 2, 3, 4];
    let s: &[u32] = &arr;
    let mut it = s.iter();
    assert!(*it.next().unwrap() == 1);
    assert!(*it.next().unwrap() == 2);
    assert!(*it.next().unwrap() == 3);
    assert!(*it.next().unwrap() == 4);
    assert!(it.next().is_none());
}

// ============================================================================
// Chaining tests: enumerate().step_by(), enumerate().take()
// ============================================================================

/// Test enumerate().step_by() to check if blanket impl is used
#[verify::test]
pub fn test_enumerate_step_by() {
    let v: [u32; 6] = [10, 20, 30, 40, 50, 60];
    let mut it = v.iter().enumerate().step_by(2);
    let (i0, x0) = it.next().unwrap();
    assert!(i0 == 0 && *x0 == 10);
    let (i1, x1) = it.next().unwrap();
    assert!(i1 == 2 && *x1 == 30);
}

/// Test enumerate().take()
#[verify::test]
pub fn test_enumerate_take() {
    let v: [u32; 5] = [10, 20, 30, 40, 50];
    let mut it = v.iter().enumerate().take(2);
    let (i0, x0) = it.next().unwrap();
    assert!(i0 == 0 && *x0 == 10);
    let (i1, x1) = it.next().unwrap();
    assert!(i1 == 1 && *x1 == 20);
    assert!(it.next().is_none());
}

/// Test take(n) where n > len, calling next after exhaustion
#[verify::test]
pub fn test_take_exhausted_then_next() {
    let v: [u32; 1] = [42];
    let mut it = v.iter().take(2);
    // First call: yields the element
    assert!(*it.next().unwrap() == 42);
    // Second call: inner is empty but n > 0, returns None
    assert!(it.next().is_none());
    // Third call: n is now 0, returns None
    assert!(it.next().is_none());
}

// ============================================================================
// Step trait boundary tests: observable behavior of steps_between,
// forward_checked, backward_checked via range iteration corner cases.
// ============================================================================

/// Range 0..1 yields exactly one element (forward_checked(0, 1) = Some(1))
#[verify::test]
pub fn test_range_single_element() {
    let mut it = (0u8..1u8).into_iter();
    assert!(it.next().unwrap() == 0);
    assert!(it.next().is_none());
}

/// Range at U8 max boundary: 254..255 (forward_checked(254, 1) = Some(255))
#[verify::test]
pub fn test_range_u8_near_max() {
    let mut it = (254u8..255u8).into_iter();
    assert!(it.next().unwrap() == 254);
    assert!(it.next().is_none());
}

/// Range where start > end yields nothing (steps_between returns (0, None))
#[verify::test]
pub fn test_range_u8_start_gt_end() {
    let mut it = (10u8..5u8).into_iter();
    assert!(it.next().is_none());
}

/// Range where start == end yields nothing (steps_between returns (0, Some(0)))
#[verify::test]
pub fn test_range_u8_start_eq_end() {
    let mut it = (5u8..5u8).into_iter();
    assert!(it.next().is_none());
}

/// U16 boundary: small range
#[verify::test]
pub fn test_range_u16_boundary() {
    let mut it = (0u16..3u16).into_iter();
    assert!(it.next().unwrap() == 0);
    assert!(it.next().unwrap() == 1);
    assert!(it.next().unwrap() == 2);
    assert!(it.next().is_none());
}

/// U32 near zero
#[verify::test]
pub fn test_range_u32_boundary() {
    let mut it = (0u32..2u32).into_iter();
    assert!(it.next().unwrap() == 0);
    assert!(it.next().unwrap() == 1);
    assert!(it.next().is_none());
}

/// U64 mid-range
#[verify::test]
pub fn test_range_u64_boundary() {
    let mut it = (100u64..103u64).into_iter();
    assert!(it.next().unwrap() == 100);
    assert!(it.next().unwrap() == 101);
    assert!(it.next().unwrap() == 102);
    assert!(it.next().is_none());
}

/// usize with start > end
#[verify::test]
pub fn test_range_usize_start_gt_end() {
    let mut it = (10usize..5usize).into_iter();
    assert!(it.next().is_none());
}

/// StepBy with step larger than range (forward_checked overflow → None, range exhausts)
#[verify::test]
pub fn test_step_by_larger_than_range() {
    let mut it = (0u8..3u8).step_by(10);
    assert!(it.next().unwrap() == 0);
    assert!(it.next().is_none());
}

/// StepBy where step exactly equals range length
#[verify::test]
pub fn test_step_by_exact_range() {
    let mut it = (0u8..5u8).step_by(5);
    assert!(it.next().unwrap() == 0);
    assert!(it.next().is_none());
}

/// StepBy(1) is same as regular iteration
#[verify::test]
pub fn test_step_by_one() {
    let mut it = (0u8..4u8).step_by(1);
    assert!(it.next().unwrap() == 0);
    assert!(it.next().unwrap() == 1);
    assert!(it.next().unwrap() == 2);
    assert!(it.next().unwrap() == 3);
    assert!(it.next().is_none());
}

/// StepBy on empty range
#[verify::test]
pub fn test_step_by_empty() {
    let mut it = (5u8..5u8).step_by(3);
    assert!(it.next().is_none());
}

/// StepBy(2) on odd-length range: last element not yielded
#[verify::test]
pub fn test_step_by_odd_range() {
    let mut it = (0u8..5u8).step_by(2);
    assert!(it.next().unwrap() == 0);
    assert!(it.next().unwrap() == 2);
    assert!(it.next().unwrap() == 4);
    assert!(it.next().is_none());
}

/// StepBy near U8 max
#[verify::test]
pub fn test_step_by_u8_near_max() {
    let mut it = (250u8..255u8).step_by(2);
    assert!(it.next().unwrap() == 250);
    assert!(it.next().unwrap() == 252);
    assert!(it.next().unwrap() == 254);
    assert!(it.next().is_none());
}

// ============================================================================
// RangeInclusive tests
// ============================================================================

/// RangeInclusive `a..=b` yields a, a+1, ..., b (inclusive)
#[verify::test]
pub fn test_range_inclusive_basic() {
    let mut it = 1usize..=3usize;
    assert!(it.next().unwrap() == 1);
    assert!(it.next().unwrap() == 2);
    assert!(it.next().unwrap() == 3);
    assert!(it.next().is_none());
}

/// RangeInclusive `a..=a` yields exactly one element
#[verify::test]
pub fn test_range_inclusive_singleton() {
    let mut it = 7usize..=7usize;
    assert!(it.next().unwrap() == 7);
    assert!(it.next().is_none());
}

/// RangeInclusive `a..=b` with a > b is empty
#[verify::test]
pub fn test_range_inclusive_empty() {
    let mut it = 5usize..=3usize;
    assert!(it.next().is_none());
}
