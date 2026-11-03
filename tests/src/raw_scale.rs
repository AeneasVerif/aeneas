//@ [!lean] skip
//@ [lean] aeneas-args=-loops-to-rec
//@ [lean] known-failure

//! Paper example: aligned rows, shared unsafe kernels, two safe calling conventions.
//! Rust arithmetic wraps, but the intended step contracts assume, in Nat:
//! src_initial[i] <= B and k * B <= u32::MAX. Thus every product is exact:
//! dst[i] = k * src_initial[i], with no overflow or modulo in the postcondition.
//! For matrices, use factors[r] * B <= u32::MAX for every row r.
//! These are proof preconditions, not runtime checks or safety requirements.
//!
//! Proof story: verify scale_raw once, frame each call inside scale_rows_raw,
//! then hide the heap behind safe wrappers with functional contracts.
//! The final variant also crosses raw -> safe -> raw before returning safely.
//! This is a Rust fixture, not a claim of completed extraction or Lean proofs.
//! See tests/lean/EXTRACTION.md for the current extraction blockers.

/// A logical [u32; 13], backed by sixteen initialized, 256-bit-aligned lanes.
/// The three hidden zero lanes are fields, not compiler padding.
#[repr(C, align(32))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Row13([u32; 16]);

impl Row13 {
    pub const fn zero() -> Self {
        Self([0; 16])
    }

    pub fn new(values: [u32; 13]) -> Self {
        let mut row = Self::zero();
        row.0[..13].copy_from_slice(&values);
        row
    }

    pub fn as_array(&self) -> &[u32; 13] {
        self.0.first_chunk::<13>().unwrap()
    }

    pub fn as_mut_array(&mut self) -> &mut [u32; 13] {
        self.0.first_chunk_mut::<13>().unwrap()
    }
}

/// # Safety
/// For nonzero N, src and dst must start at 32-byte-aligned addresses and
/// permit reading N initialized u32s / writing N u32s respectively, with valid
/// in-allocation pointer arithmetic. Their ranges must be disjoint or use the
/// same pointer (up to constness). No other access may conflict.
/// All N elements, including any explicit padding lanes, must be real u32s.
/// For N == 0, neither pointer is accessed or used for arithmetic.
pub unsafe fn scale_raw<const N: usize>(k: u32, src: *const u32, dst: *mut u32) {
    for i in 0..N {
        unsafe {
            // Read before writing: in-place execution preserves the unread suffix.
            let value = src.add(i).read();
            dst.add(i).write(k.wrapping_mul(value));
        }
    }
}

/// Disjoint mode: preserve src and replace dst by its scaled contents.
pub fn scale_into(k: u32, src: &Row13, dst: &mut Row13) {
    // The safe borrows supply disjoint readable/writable ranges.
    unsafe { scale_raw::<16>(k, src.0.as_ptr(), dst.0.as_mut_ptr()) };
}

/// Equal mode: one exclusive range supplies both read and write permissions.
pub fn scale_in_place(k: u32, buf: &mut Row13) {
    let p = buf.0.as_mut_ptr();
    // No overlapping shared/mutable Rust references are manufactured.
    unsafe { scale_raw::<16>(k, p, p) };
}

/// Shared matrix loop: pointer arithmetic advances by the padded row stride.
///
/// # Safety
/// src and dst must permit reading/writing R rows respectively.
/// The row ranges must be disjoint or identical, with valid pointer arithmetic;
/// source elements must be initialized. No conflicting accesses are allowed,
/// including overlap between factors and the destination elements.
pub unsafe fn scale_rows_raw<const R: usize>(
    factors: &[u32; R],
    src: *const Row13,
    dst: *mut Row13,
) {
    for r in 0..R {
        unsafe {
            scale_raw::<16>(factors[r], src.add(r).cast(), dst.add(r).cast());
        }
    }
}

/// Functional contract: dst[r][i] = factors[r] * src_initial[r][i].
pub fn scale_rows_into<const R: usize>(factors: &[u32; R], src: &[Row13; R], dst: &mut [Row13; R]) {
    unsafe { scale_rows_raw(factors, src.as_ptr(), dst.as_mut_ptr()) };
}

/// The same row specification, with a single matrix supplying both roles.
pub fn scale_rows_in_place<const R: usize>(factors: &[u32; R], rows: &mut [Row13; R]) {
    let p = rows.as_mut_ptr();
    unsafe { scale_rows_raw(factors, p, p) };
}

/// Pure safe helper for the reverse-boundary variant; no pointer operations.
pub fn scale_slice(k: u32, buf: &mut [u32]) {
    let mut i = 0;
    while i < buf.len() {
        buf[i] = k.wrapping_mul(buf[i]);
        i += 1;
    }
}

/// Temporarily lend raw storage to safe code, then observe its update raw.
///
/// # Safety
/// p must permit exclusive access to sixteen initialized u32s in one allocation,
/// satisfying slice::from_raw_parts_mut's requirements and the subsequent read.
pub unsafe fn scale_via_borrow_raw(k: u32, p: *mut u32) -> u32 {
    {
        let borrowed = unsafe { core::slice::from_raw_parts_mut(p, 16) };
        scale_slice(k, borrowed);
    }
    // The matching backward computation must restore raw access before this read.
    unsafe { p.read() }
}

/// Safe -> raw -> safe helper -> raw observation -> safe updated buffer.
pub fn scale_via_borrow(k: u32, buf: &mut Row13) -> u32 {
    unsafe { scale_via_borrow_raw(k, buf.0.as_mut_ptr()) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expected(k: u32, values: &[u32]) -> Vec<u32> {
        values
            .iter()
            .map(|&x| ((u64::from(k) * u64::from(x)) % (1u64 << 32)) as u32)
            .collect()
    }

    #[test]
    fn both_modes_and_reverse_boundary() {
        fn check(src: Row13) {
            for k in [0, 1, 2, 19, u32::MAX] {
                let want = expected(k, &src.0);
                let mut dst = Row13::zero();
                scale_into(k, &src, &mut dst);
                assert_eq!(dst.0.as_slice(), want);
                let mut same = src;
                scale_in_place(k, &mut same);
                assert_eq!(same, dst);
                let mut borrowed = src;
                assert_eq!(scale_via_borrow(k, &mut borrowed), want[0]);
                assert_eq!(borrowed, dst);
            }
        }
        check(Row13::zero());
        let values = std::array::from_fn(|i| [0, 1, 17, u32::MAX, 0x8000_0000][i % 5]);
        check(Row13::new(values));
    }

    #[test]
    fn subranges_of_one_allocation_preserve_the_frame() {
        let mut storage = [
            Row13::new([91; 13]),
            Row13::new([2; 13]),
            Row13::zero(),
            Row13::new([93; 13]),
        ];
        let (left, right) = storage.split_at_mut(2);
        let src = left.last_chunk::<1>().unwrap();
        let dst = right.first_chunk_mut::<1>().unwrap();
        scale_rows_into(&[7], src, dst);
        assert_eq!(dst[0], Row13::new([14; 13]));
        scale_rows_in_place(&[3], dst);
        assert_eq!(dst[0], Row13::new([42; 13]));
        assert_eq!(scale_via_borrow(2, &mut dst[0]), 84);
        assert_eq!(
            storage,
            [
                Row13::new([91; 13]),
                Row13::new([2; 13]),
                Row13::new([84; 13]),
                Row13::new([93; 13]),
            ]
        );
    }

    #[test]
    fn row_composition_and_empty_dimensions() {
        let src = [
            Row13::new([1; 13]),
            Row13::new([4; 13]),
            Row13::new([7; 13]),
        ];
        let factors = [2, 0, u32::MAX];
        let mut dst = [Row13::zero(); 3];
        scale_rows_into(&factors, &src, &mut dst);
        for r in 0..src.len() {
            assert_eq!(dst[r].0.as_slice(), expected(factors[r], &src[r].0));
        }
        let mut same = src;
        scale_rows_in_place(&factors, &mut same);
        assert_eq!(same, dst);
        scale_rows_into(&[], &[], &mut []);
        scale_rows_in_place(&[], &mut []);
        unsafe { scale_raw::<0>(7, core::ptr::null(), core::ptr::null_mut()) };
    }

    #[test]
    fn aligned_padded_rows_and_bounded_products() {
        let src = Box::new([Row13::new([65535; 13]), Row13::new([12345; 13])]);
        let mut dst = Box::new([Row13::zero(); 2]);
        for r in 0..2 {
            assert_eq!(src[r].0.as_ptr().addr() % 32, 0);
            assert_eq!(dst[r].0.as_ptr().addr() % 32, 0);
        }
        assert_eq!(src[1].0.as_ptr().addr() - src[0].0.as_ptr().addr(), 64);
        let factors = [65535, 17];
        scale_rows_into(&factors, &src, &mut dst);
        for r in 0..2 {
            for i in 0..16 {
                let exact = u64::from(factors[r]) * u64::from(src[r].0[i]);
                assert!(exact <= u64::from(u32::MAX));
                assert_eq!(u64::from(dst[r].0[i]), exact);
            }
            assert_eq!(&dst[r].0[13..], &[0; 3]);
        }
    }

    #[test]
    fn client_array_updates_preserve_hidden_zero_lanes() {
        let mut row = Row13::new([1; 13]);
        let view: &mut [u32; 13] = row.as_mut_array();
        *view = [7; 13];
        scale_in_place(3, &mut row);
        assert_eq!(row.as_array(), &[21; 13]);
        assert_eq!(&row.0[13..], &[0; 3]);
    }
}
