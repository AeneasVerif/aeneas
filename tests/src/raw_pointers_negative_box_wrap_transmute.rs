//@ [!lean] skip
//@ [lean] known-failure
//! `BoxWrap` is translated to an alias of `U64`: transmuting it is rejected.

pub struct BoxWrap(Box<u64>);

pub fn f(b: BoxWrap) -> u64 {
    unsafe { std::mem::transmute::<BoxWrap, u64>(b) }
}
