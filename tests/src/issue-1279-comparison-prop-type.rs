//@ [!lean] skip

//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1260
//!
//! Boolean variables must be typed with `: Bool` to ensure they do not
//! get inferred as `Prop`

pub struct Access {
    pub start: u64,
    pub size: u64,
}

impl Access {
    pub fn end(&self) -> u64 {
        self.start + self.size
    }

    pub fn overlaps(&self, other: &Access) -> bool {
        !(self.end() <= other.start || self.start >= other.end())
    }
}
