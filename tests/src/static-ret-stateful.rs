//@ [!lean] skip
//! A function returning the `'static` result of a trait method, in a crate which uses raw
//! pointers: the call to the trait method makes the function stateful, and the region
//! abstraction of the call owns the static region, which can not be ended early.

pub unsafe fn read(p: *const u8) -> u8 {
    *p
}

const NAN: &str = "NaN";

pub trait Float: Copy {
    fn format_nonfinite(self) -> &'static str;
}

impl Float for u32 {
    fn format_nonfinite(self) -> &'static str {
        NAN
    }
}

pub struct Buffer {
    pub bytes: [u8; 4],
}

impl Buffer {
    pub fn format<F: Float>(&mut self, f: F, b: bool) -> &str {
        if b {
            f.format_nonfinite()
        } else {
            self.format_finite()
        }
    }

    pub fn format_finite(&mut self) -> &str {
        "x"
    }
}
