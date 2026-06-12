//@ [!lean] skip
use std::num::NonZeroU8;

pub fn get_inner(x: NonZeroU8) -> u8 {
    x.get()
}
