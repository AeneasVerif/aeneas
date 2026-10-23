//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] no-check-output

pub trait Width {
    const WIDTH: u32;
}
impl Width for u8 {
    const WIDTH: u32 = 8;
}
pub struct Word<T>(pub T);
pub trait Cross {
    const SOURCE: u32;
    const BASE: u32 = Self::SOURCE;
    const VALUE: u32;
}
impl<T: Width> Cross for Word<T> {
    const SOURCE: u32 = T::WIDTH;
    const VALUE: u32 = Self::BASE + <Word<u8> as Cross>::BASE;
}
