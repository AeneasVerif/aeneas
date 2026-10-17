//@ [!lean] skip
//! The initializer of a global reads a table through a raw pointer (as zmij's
//! `STATIC_DATA`). Rust evaluates it at compile time: it only reads constant data
//! and leaves no effect on the heap, so it is translated like a function, and
//! evaluated where the global is used.

const TABLE: [u64; 4] = [1, 2, 3, 4];

const fn compute(i: usize) -> u64 {
    unsafe { *TABLE.as_ptr().add(i) }
}

pub struct Data {
    pub a: u64,
    pub b: u64,
}

pub static DATA: Data = Data {
    a: compute(1),
    b: compute(3),
};

pub fn sum() -> u64 {
    DATA.a + DATA.b
}
