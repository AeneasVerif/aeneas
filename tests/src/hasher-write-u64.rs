//@ [!lean] skip
//! A `Hasher` which only implements `write`: `write_u64` is the default method,
//! which writes the bytes of the integer.
use core::hash::Hasher;

pub struct Sum(pub u64);

impl Hasher for Sum {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        let mut i = 0;
        while i < bytes.len() {
            self.0 = self.0.wrapping_add(bytes[i] as u64);
            i += 1;
        }
    }
}

pub fn hash_u64(i: u64) -> u64 {
    let mut h = Sum(0);
    h.write_u64(i);
    h.finish()
}

pub struct Fx(pub u64);

impl Hasher for Fx {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _bytes: &[u8]) {}
    fn write_u64(&mut self, i: u64) {
        self.0 ^= i;
    }
}
