//@ [!lean] skip
//! A simplified version of SymCrust's `InPlaceOrDisjointBuffer`: a buffer which
//! reads from a source and writes to a destination, which are either the same
//! slice or two disjoint slices.
use std::marker::PhantomData;

pub struct InPlaceOrDisjointBuffer<'a, T> {
    src: *const T,
    dst: *mut T,
    len: usize,
    _phantom: PhantomData<&'a mut [T]>,
}

impl<'a, T> InPlaceOrDisjointBuffer<'a, T> {
    pub fn new_in_place(buffer: &'a mut [T]) -> Self {
        // Remark: we read the length before converting the borrow to a raw
        // pointer, because Aeneas invalidates the raw pointer as soon as the
        // borrow is used again.
        let len = buffer.len();
        let ptr = buffer.as_mut_ptr();
        Self {
            src: ptr as *const T,
            dst: ptr,
            len,
            _phantom: PhantomData,
        }
    }

    // Remark: [src] should be a shared borrow, but Aeneas invalidates the raw
    // pointers obtained from shared borrows (through a reborrow) when the
    // function which created them returns.
    pub fn new_disjoint(src: &'a mut [T], dst: &'a mut [T]) -> Self {
        assert_eq!(src.len(), dst.len());
        let len = src.len();
        Self {
            src: src.as_mut_ptr() as *const T,
            dst: dst.as_mut_ptr(),
            len,
            _phantom: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn src(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.src, self.len) }
    }

    pub fn dst(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.dst, self.len) }
    }
}

pub fn zero_first_in_place(buf: &mut [u8]) -> usize {
    let mut b = InPlaceOrDisjointBuffer::new_in_place(buf);
    let d = b.dst();
    d[0] = 0;
    b.len()
}

pub fn copy_first(src: &mut [u8], dst: &mut [u8]) {
    let mut b = InPlaceOrDisjointBuffer::new_disjoint(src, dst);
    let x = b.src()[0];
    b.dst()[0] = x;
}

pub fn increment_first_in_place(buf: &mut [u8]) {
    let mut b = InPlaceOrDisjointBuffer::new_in_place(buf);
    let x = b.src()[0];
    b.dst()[0] = x.wrapping_add(1);
}
