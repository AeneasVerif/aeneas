//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub trait Bits {
    const WIDTH: u32;
    const SHIFT: u32 = Self::WIDTH - 1;
    const MASK: u64;
    const NEXT: u64 = Self::MASK + 1;
}

impl Bits for u8 {
    const WIDTH: u32 = 8;
    const MASK: u64 = 1 << Self::SHIFT;
}

impl<const N: usize> Bits for [u8; N] {
    const WIDTH: u32 = N as u32;
    const MASK: u64 = 1 << Self::SHIFT;
}

pub trait Width {
    const WIDTH: u32;
}
impl Width for u8 {
    const WIDTH: u32 = 8;
}
impl Width for u16 {
    const WIDTH: u32 = 16;
}

pub struct Word<T>(pub T);
impl<T: Width> Bits for Word<T> {
    const WIDTH: u32 = T::WIDTH;
    const MASK: u64 = 1 << Self::SHIFT;
}

pub trait Mixed {
    const VALUE: u32;
}
impl<T: Width> Mixed for Word<T> {
    const VALUE: u32 = T::WIDTH + <Word<u8> as Bits>::WIDTH;
}

pub fn mask<T: Bits>() -> u64 {
    T::MASK
}
pub fn next<T: Bits>() -> u64 {
    T::NEXT
}
pub fn mixed<T: Width>() -> u32 {
    <Word<T> as Mixed>::VALUE
}

// A reference to another instantiation of the same impl must keep its arguments.
pub trait Cross {
    const BASE: u32;
    const VALUE: u32;
}
impl<T: Width> Cross for Word<T> {
    const BASE: u32 = T::WIDTH;
    const VALUE: u32 = Self::BASE + <Word<u8> as Cross>::BASE;
}
pub fn cross<T: Width>() -> u32 {
    <Word<T> as Cross>::VALUE
}

#[verify::test]
pub fn regression() {
    assert!(mask::<u8>() == 128);
    assert!(next::<u8>() == 129);
    assert!(mask::<[u8; 6]>() == 32);
    assert!(next::<[u8; 6]>() == 33);
    assert!(mask::<Word<u8>>() == 128);
    assert!(mask::<Word<u16>>() == 32768);
    assert!(next::<Word<u16>>() == 32769);
    assert!(mixed::<u8>() == 16);
    assert!(mixed::<u16>() == 24);
    assert!(cross::<u8>() == 16);
    assert!(cross::<u16>() == 24);
}

#[cfg(test)]
#[test]
fn rust_regression() {
    regression();
}
