use crate::util::double;

pub struct Point {
    pub x: u32,
    pub y: u32,
}

pub fn stretched_sum(p: &Point) -> u32 {
    double(p.x) + p.y
}
