//@ [!lean] skip
//! An implementation of a method of a trait declared in the crate which accesses
//! the heap and returns a borrow (as itoa's `Sealed::write`): the method is
//! stateful in the trait declaration too, and its backward function is deferred.
use core::mem::MaybeUninit;

pub trait Sealed: Copy {
    type Buffer: 'static;
    fn write(self, buf: &mut Self::Buffer) -> &str;
}

impl Sealed for u8 {
    type Buffer = [MaybeUninit<u8>; 3];
    fn write(self, buf: &mut [MaybeUninit<u8>; 3]) -> &str {
        let p = buf.as_mut_ptr() as *mut u8;
        unsafe {
            *p = b'0' + self % 10;
            let s = core::slice::from_raw_parts(p, 1);
            core::str::from_utf8_unchecked(s)
        }
    }
}

pub struct Buffer {
    bytes: [MaybeUninit<u8>; 3],
}

impl Buffer {
    pub fn format(&mut self, i: u8) -> &str {
        i.write(&mut self.bytes)
    }
}
