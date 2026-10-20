//@ [!lean] skip
//! Uninitialized memory: `MaybeUninit` values, and buffers of `MaybeUninit`
//! initialized through raw pointers.
use core::mem::MaybeUninit;
use core::slice;

pub fn init_with_write() -> u32 {
    let mut a = MaybeUninit::uninit();
    a.write(3u32);
    let b = MaybeUninit::new(4u32);
    unsafe { a.assume_init() + b.assume_init() }
}

/// Reading a value which has not been initialized is undefined behavior.
pub fn assume_init_uninit() -> u64 {
    let a: MaybeUninit<u64> = MaybeUninit::uninit();
    unsafe { a.assume_init() }
}

/// Reading uninitialized memory through a raw pointer is undefined behavior.
pub fn read_uninit() -> u64 {
    let a: MaybeUninit<u64> = MaybeUninit::uninit();
    unsafe { *a.as_ptr() }
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
            let p = self.bytes.as_mut_ptr() as *mut u8;
            *p = b'o';
            *p.add(1) = b'k';
            slice::from_raw_parts(self.bytes.as_ptr() as *const u8, 2)
        }
    }

    /// Reads one byte past the initialized ones.
    pub fn fill_too_much(&mut self) -> &[u8] {
        unsafe {
            let p = self.bytes.as_mut_ptr().cast::<u8>();
            *p = b'o';
            slice::from_raw_parts(self.bytes.as_ptr().cast::<u8>(), 2)
        }
    }
}

pub fn fill_first() -> u8 {
    let mut buf = Buffer::new();
    let s = buf.fill();
    s[1]
}
