//@ [!lean] skip
//! Uninitialized memory converted to raw pointers.
use core::mem::MaybeUninit;
use core::slice;

unsafe fn write_two(p: *mut u64, q: *mut u64) {
    *p = 1;
    *q = 2;
}

/// Values initialized through raw pointers (from ryu).
fn init_through_ptrs() -> u64 {
    let mut a: MaybeUninit<u64> = MaybeUninit::uninit();
    let mut b: MaybeUninit<u64> = MaybeUninit::uninit();
    unsafe { write_two(a.as_mut_ptr(), b.as_mut_ptr()) };
    let a = unsafe { a.assume_init() };
    let b = unsafe { b.assume_init() };
    a + b
}

/// Reading a value which has not been initialized is undefined behavior.
fn read_uninit() -> u64 {
    let a: MaybeUninit<u64> = MaybeUninit::uninit();
    unsafe { a.assume_init() }
}

/// A buffer of uninitialized bytes (from ryu).
pub struct Buffer {
    bytes: [MaybeUninit<u8>; 4],
}

impl Buffer {
    pub fn new() -> Self {
        Buffer {
            bytes: [MaybeUninit::<u8>::uninit(); 4],
        }
    }

    pub fn fill(&mut self) -> &[u8] {
        unsafe {
            let p = self.bytes.as_mut_ptr().cast::<u8>();
            *p = b'o';
            *p.add(1) = b'k';
            slice::from_raw_parts(self.bytes.as_ptr().cast::<u8>(), 2)
        }
    }
}
