//@ [!lean] skip
//@ [lean] subdir=InPlaceOrDisjointBuffer
use std::marker::PhantomData;

pub struct InPlaceOrDisjointBuffer<'a, T> {
    src: *const T,
    dst: *mut T,
    len: usize,
    _phantom: PhantomData<&'a mut [T]>,
}

impl<'a, T> InPlaceOrDisjointBuffer<'a, T> {
    pub fn new_in_place(buffer: &'a mut [T]) -> Self {
        let ptr = buffer.as_mut_ptr();
        Self {
            src: ptr as *const T,
            dst: ptr,
            len: buffer.len(),
            _phantom: PhantomData,
        }
    }

    pub fn new_disjoint<const N: usize>(src: &'a [T; N], dst: &'a mut [T; N]) -> Self {
        Self {
            src: src.as_ptr(),
            dst: dst.as_mut_ptr(),
            len: N,
            _phantom: PhantomData,
        }
    }

    pub fn new_disjoint_from_slices(src: &'a [T], dst: &'a mut [T]) -> Self {
        assert_eq!(src.len(), dst.len());
        Self {
            src: src.as_ptr(),
            dst: dst.as_mut_ptr(),
            len: src.len(),
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

pub fn copy_first(src: &[u8], dst: &mut [u8]) {
    let mut b = InPlaceOrDisjointBuffer::new_disjoint_from_slices(src, dst);
    let x = b.src()[0];
    b.dst()[0] = x;
}

pub fn copy_first_disjoint(src: &[u8; 4], dst: &mut [u8; 4]) {
    let mut b = InPlaceOrDisjointBuffer::new_disjoint(src, dst);
    let x = b.src()[0];
    b.dst()[0] = x;
}

pub fn write_through_raw_ptr(x: &mut [u8]) {
    let n = x.len();
    let p = x.as_mut_ptr();
    let s = unsafe { core::slice::from_raw_parts_mut(p, n) };
    s[0] = 1;
}
