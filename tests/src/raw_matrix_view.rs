//@ [!lean] skip
//@ [lean] aeneas-args=-loops-to-rec
//@ [lean] known-failure

//! Matrix <-> flat view: two logical 13-lane rows, physically two 16-lane rows.
//! All 32 lanes are initialized u32 fields; there is no compiler padding.
//! The intended specification assumes k * input[r][c] <= u32::MAX in Nat.
//! Then multiplication is exact, the three zero lanes per row stay zero,
//! and the safe and raw versions agree, including the returned last element.

#[repr(C, align(32))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Matrix([[u32; 16]; 2]);

impl Matrix {
    /// Hide the padded representation: clients supply only the logical elements.
    pub fn new(rows: [[u32; 13]; 2]) -> Self {
        let mut matrix = Self([[0; 16]; 2]);
        for r in 0..2 {
            matrix.0[r][..13].copy_from_slice(&rows[r]);
        }
        matrix
    }

    pub fn row(&self, r: usize) -> &[u32; 13] {
        self.0[r].first_chunk::<13>().unwrap()
    }

    pub fn row_mut(&mut self, r: usize) -> &mut [u32; 13] {
        self.0[r].first_chunk_mut::<13>().unwrap()
    }
}

/// Pure safe computation, shared by the two view implementations.
pub fn scale_slice(k: u32, values: &mut [u32]) {
    let mut i = 0;
    while i < values.len() {
        values[i] = k.wrapping_mul(values[i]);
        i += 1;
    }
}

/// Reference implementation: safe flattening already preserves the matrix shape.
pub fn scale_safe(k: u32, matrix: &mut Matrix) -> u32 {
    scale_slice(k, matrix.0.as_flattened_mut());
    matrix.0[1][12]
}

/// # Safety
/// matrix must designate an initialized, exclusively accessible Matrix throughout
/// this call. Its repr(C) payload starts at offset zero, has no padding, and is
/// 32-byte aligned. Each row has a 64-byte stride. No allocation is created here.
pub unsafe fn scale_raw(k: u32, matrix: *mut Matrix) -> u32 {
    {
        // A temporary flat borrow of the *whole* matrix, not just its first row.
        let flat = unsafe { core::slice::from_raw_parts_mut(matrix.cast::<u32>(), 32) };
        scale_slice(k, flat);
    }
    // Return the flat borrow before reading through the original matrix pointer.
    // The Lean translation must call its matching effectful backward function here.
    unsafe { matrix.read().0[1][12] }
}

/// Safe caller: the matching outer backward function restores the updated matrix.
pub fn scale(k: u32, matrix: &mut Matrix) -> u32 {
    unsafe { scale_raw(k, matrix) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_and_safe_views_agree_and_preserve_padding() {
        for k in [0, 1, 17, u32::MAX] {
            let rows = std::array::from_fn(|r| {
                std::array::from_fn(|c| [0, 1, 65535, u32::MAX][(r + c) % 4])
            });
            let mut raw = Matrix::new(rows);
            let mut safe = raw;
            assert_eq!(scale(k, &mut raw), scale_safe(k, &mut safe));
            assert_eq!(raw, safe);
            for r in 0..2 {
                for c in 0..13 {
                    let exact = u64::from(k) * u64::from(rows[r][c]);
                    assert_eq!(u64::from(raw.row(r)[c]), exact % (1u64 << 32));
                }
                assert_eq!(&raw.0[r][13..], &[0; 3]);
            }
        }
    }

    #[test]
    fn bounded_products_and_surrounding_frame() {
        let original = Matrix::new([[12345; 13], [65535; 13]]);
        let mut storage = [original; 3];
        assert_eq!(scale(65535, &mut storage[1]), 65535 * 65535);
        assert_eq!(storage[0], original);
        assert_eq!(storage[2], original);
        for r in 0..2 {
            for c in 0..13 {
                assert_eq!(
                    u64::from(storage[1].row(r)[c]),
                    65535 * u64::from(original.row(r)[c])
                );
            }
        }
    }

    #[test]
    fn layout_is_fully_initialized_and_vector_aligned() {
        assert_eq!(core::mem::size_of::<Matrix>(), 128);
        assert_eq!(core::mem::align_of::<Matrix>(), 32);
        let matrix = Box::new(Matrix::new([[1; 13], [2; 13]]));
        for r in 0..2 {
            assert_eq!(matrix.0[r].as_ptr().addr() % 32, 0);
        }
        assert_eq!(
            matrix.0[1].as_ptr().addr() - matrix.0[0].as_ptr().addr(),
            64
        );
        assert_eq!(matrix.0.as_flattened().len() * 4, 128);
    }
}
