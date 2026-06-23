//@ [!lean] skip
//@ charon-args=--opaque=crate::wipe_slice

//! Regression test for a bug where activating a reserved (two-phase) mutable
//! borrow fails when the target shared loan is nested inside an outer shared
//! loan created by subsequent shared borrows of the parent struct.
//!
//! The pattern:
//!   self.inner.method(self.get_x(), self.get_y())
//! compiles to LLBC as:
//!   1. _tmp = &two-phase-mut self.inner   (reserved borrow, creates SL on inner)
//!   2. _ref = &*self                      (shared borrow of whole struct -> outer SL)
//!   3. _x = get_x(move _ref)             (call keeps SL alive via abstraction)
//!   4. _ref2 = &*self                     (another shared borrow)
//!   5. _y = get_y(move _ref2)
//!   6. Inner::method(move _tmp, _x, _y)  (activates reserved borrow -> BUG)
//! At step 6, the inner SL is inside the outer SL, but promote_reserved_mut_borrow
//! searches with enter_shared_loans=false and cannot find it.

fn wipe_slice<T>(s: &mut [T]) {
    // Opaque to the analyzer (via charon --opaque flag).
    // Mimics the real wipe_slice which uses raw pointers internally.
    let _len = s.len();
}

struct Inner {
    buf: [u8; 4],
}

impl Drop for Inner {
    fn drop(&mut self) {
        wipe_slice(&mut self.buf);
    }
}

impl Inner {
    fn init(&mut self, block_size: u32, pad_value: u8) {
        wipe_slice(&mut self.buf);
    }
}

struct Outer {
    inner: Inner,
    block_size: u32,
    pad_value: u8,
}

impl Outer {
    fn get_block_size(&self) -> u32 {
        self.block_size
    }

    fn get_pad_value(&self) -> u8 {
        self.pad_value
    }

    /// This triggers the bug: the two-phase borrow on self.inner is created
    /// first, then shared borrows on the whole struct (for the arguments)
    /// wrap the entire value in a shared loan, trapping the inner loan.
    fn init(&mut self) {
        self.inner.init(self.get_block_size(), self.get_pad_value());
    }
}

// Variant without Drop: verifies the bug is triggered by the two-phase borrow
// nesting pattern alone, independent of Drop trait implementation.
struct InnerNoDrop {
    buf: [u8; 4],
}

impl InnerNoDrop {
    fn init(&mut self, block_size: u32, pad_value: u8) {
        wipe_slice(&mut self.buf);
    }
}

struct OuterNoDrop {
    inner: InnerNoDrop,
    block_size: u32,
    pad_value: u8,
}

impl OuterNoDrop {
    fn get_block_size(&self) -> u32 {
        self.block_size
    }

    fn get_pad_value(&self) -> u8 {
        self.pad_value
    }

    fn init(&mut self) {
        self.inner.init(self.get_block_size(), self.get_pad_value());
    }
}
