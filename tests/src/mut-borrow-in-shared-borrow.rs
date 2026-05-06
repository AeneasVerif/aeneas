//@ [!lean] skip
//! Minimal examples of mutable borrows inside shared borrows.
//!
//! These test that Aeneas correctly handles mutable references appearing below
//! shared references in function signatures (e.g., `&self` on a struct containing
//! `&'a mut T`). The mutable borrows are frozen by the shared context.
//!
//! Minimized from SymCrypt's InPlaceOrDisjointBuffer<'a, T> which stores
//! PhantomData<&'a mut [T]> and has methods taking &self.

// ============================================================
// Example 1: Simplest case — struct with &'a mut field, method taking &self
// ============================================================

struct MutFieldAccessViaShared<'a> {
    data: &'a mut u32,
}

impl<'a> MutFieldAccessViaShared<'a> {
    /// Taking &self on a struct containing &'a mut creates a shared borrow
    /// above a mutable borrow.
    fn get(&self) -> u32 {
        *self.data
    }
}

fn use_mut_field_access_via_shared() {
    let mut x: u32 = 42;
    let w = MutFieldAccessViaShared { data: &mut x };
    let _v = w.get();
}

/// Receives the mutable borrow as input — should produce a backward function
/// that gives back the &'a mut u32.
fn use_mut_field_access_via_shared_param(x: &mut u32) -> u32 {
    let w = MutFieldAccessViaShared { data: x };
    w.get()
}

// ============================================================
// Example 2: Struct with &'a mut slice, method taking &self returns length
// ============================================================

struct SliceWrapper<'a, T> {
    buf: &'a mut [T],
}

impl<'a, T> SliceWrapper<'a, T> {
    fn len(&self) -> usize {
        self.buf.len()
    }

    fn first(&self) -> Option<&T> {
        self.buf.first()
    }
}

fn use_slice_wrapper() {
    let mut data = [1u32, 2, 3];
    let w = SliceWrapper { buf: &mut data };
    let _len = w.len();
}

/// Receives the mutable slice as input — should produce a backward function
/// that gives back the &'a mut [T].
fn use_slice_wrapper_param(buf: &mut [u32]) -> usize {
    let w = SliceWrapper { buf };
    w.len()
}

// ============================================================
// Example 3: Two-field struct with shared and mutable borrows
// ============================================================

struct MixedBorrows<'a, T> {
    shared: &'a [T],
    mutable: &'a mut [T],
}

impl<'a, T> MixedBorrows<'a, T> {
    fn shared_len(&self) -> usize {
        self.shared.len()
    }

    fn mutable_len(&self) -> usize {
        self.mutable.len()
    }
}

fn use_mixed_borrows() {
    let shared_data = [1u32, 2, 3];
    let mut mut_data = [4u32, 5, 6];
    let w = MixedBorrows {
        shared: &shared_data,
        mutable: &mut mut_data,
    };
    let _s = w.shared_len();
    let _m = w.mutable_len();
}

/// Receives both borrows as inputs — should produce a backward function only
/// for the mutable borrow, not the shared one.
fn use_mixed_borrows_param(shared: &[u32], mutable: &mut [u32]) -> (usize, usize) {
    let w = MixedBorrows { shared, mutable };
    (w.shared_len(), w.mutable_len())
}
