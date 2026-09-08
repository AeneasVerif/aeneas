//@ [!lean] skip

//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1260
//!
//! A matchless shared loan in a frozen input abstraction must remain unchanged
//! while computing a loop fixed point.

pub fn f<'a>(mut x: &'a u32, y: &'a u32) -> u32 {
    let mut s = *x;
    x = y;
    let mut i = 0u32;
    loop {
        s = s.wrapping_add(*x);
        i = i.wrapping_add(1);
        if i > 10 {
            return s;
        }
    }
}
