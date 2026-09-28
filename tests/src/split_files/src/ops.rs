//! Depends on `types` only: its Lean module imports the `Types` module.

use crate::types::Point;

pub fn sum(p: &Point) -> i32 {
    p.x + p.y
}
