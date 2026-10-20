//@ [!lean] skip
//@ [lean] known-failure
//! Transmuting a reference is rejected (references are erased).

pub fn f(x: &u64) -> u64 {
    unsafe { std::mem::transmute::<&u64, u64>(x) }
}
