//@ [!lean] skip
//@ [lean] subdir=InPlaceOrDisjointBuffer
use core::ptr;
use std::marker::PhantomData;

pub type Block = [u8; 16];

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

    pub unsafe fn from_raw_parts(src: *const T, dst: *mut T, len: usize) -> Self {
        Self {
            src,
            dst,
            len,
            _phantom: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub unsafe fn loadu_block_src(&self, offset: usize) -> Block {
        ptr::read_unaligned(self.src.add(offset) as *const Block)
    }

    pub unsafe fn loadu_block_dst(&self, offset: usize) -> Block {
        ptr::read_unaligned(self.dst.add(offset) as *const Block)
    }

    pub unsafe fn storeu_block(&mut self, offset: usize, value: Block) {
        ptr::write_unaligned(self.dst.add(offset) as *mut Block, value)
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

pub fn wipe(pb_data: *mut u8, cb_data: usize) {
    unsafe { ptr::write_bytes(pb_data, 0, cb_data) }
}

pub fn wipe_words(pb_dst: &mut [u32]) {
    wipe(pb_dst.as_mut_ptr().cast(), pb_dst.len() * 4);
}

pub fn copy_block_in_place(data: &mut [u8; 32]) {
    let mut b = InPlaceOrDisjointBuffer::new_in_place(data);
    unsafe {
        let v = b.loadu_block_src(0);
        b.storeu_block(16, v);
    }
}

pub fn xor_block_disjoint(src: &[u8; 16], dst: &mut [u8; 16]) {
    let mut b = InPlaceOrDisjointBuffer::new_disjoint(src, dst);
    unsafe {
        let s = b.loadu_block_src(0);
        let mut d = b.loadu_block_dst(0);
        d[0] ^= s[0];
        b.storeu_block(0, d);
    }
}

pub fn copy_words_from_raw_parts(src: &[u32; 4], dst: &mut [u32; 4]) {
    unsafe {
        let mut b = InPlaceOrDisjointBuffer::from_raw_parts(src.as_ptr(), dst.as_mut_ptr(), 4);
        let v = b.loadu_block_src(0);
        b.storeu_block(0, v);
    }
}

pub fn const_time_slices_equal(a: &[u8], b: &[u8]) -> bool {
    assert_eq!(a.len(), b.len());
    unsafe { const_time_slices_equal_impl(a, b) }
}

unsafe fn const_time_slices_equal_impl(a: &[u8], b: &[u8]) -> bool {
    debug_assert_eq!(a.len(), b.len());

    let len = a.len();
    let mut diff: u8 = 0;

    for i in 0..len {
        let ai = unsafe { core::ptr::read_volatile(a.as_ptr().add(i)) };
        let bi = unsafe { core::ptr::read_volatile(b.as_ptr().add(i)) };
        diff |= ai ^ bi;
    }

    diff == 0
}

pub fn const_time_slice_copy(a: &[u8], b: &mut [u8], copy_size: u32) {
    assert_eq!(a.len(), b.len());
    unsafe {
        const_time_slice_copy_impl(a, b, copy_size);
    }
}

unsafe fn const_time_slice_copy_impl(a: &[u8], b: &mut [u8], copy_size: u32) {
    debug_assert_eq!(a.len(), b.len());

    let len = a.len();

    for i in 0..len {
        let ai = unsafe { core::ptr::read_volatile(a.as_ptr().add(i)) };
        let mut bi = unsafe { core::ptr::read_volatile(b.as_ptr().add(i)) };
        let mask = (((i as u32).wrapping_sub(copy_size) as i32) >> 31) as u8;
        bi ^= (ai ^ bi) & mask;
        unsafe { core::ptr::write_volatile(b.as_mut_ptr().add(i), bi) };
    }
}
