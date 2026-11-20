//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods
// Without filtering, the generic `rev()` call emits an `Iterator::rev` field;
// the Lean `Iterator` model cannot contain that field because it would be recursive.
#![feature(register_tool)]
#![register_tool(verify)]

// The deliberately different rfold result makes method dispatch observable.
struct Odd {
    remaining: bool,
}

impl Iterator for Odd {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        if self.remaining {
            self.remaining = false;
            Some(1)
        } else {
            None
        }
    }
}

impl DoubleEndedIterator for Odd {
    fn next_back(&mut self) -> Option<u32> {
        if self.remaining {
            self.remaining = false;
            Some(1)
        } else {
            None
        }
    }

    fn rfold<B, F>(self, init: B, mut f: F) -> B
    where
        F: FnMut(B, u32) -> B,
    {
        f(init, 99)
    }
}

#[verify::test]
pub fn rfold_slice() {
    let values = [1u32, 2, 3];
    let value = values.iter().rfold(0u32, |acc, item| acc * 10 + *item);
    assert!(value == 321);
}

#[verify::test]
pub fn rfold_slice_last() {
    let values = [1u32, 2, 3];
    let value = values.iter().rfold(0u32, |_, item| *item);
    assert!(value == 1);
}

#[verify::test]
pub fn rev_fold_slice() {
    let values = [1u32, 2, 3];
    let value = values.iter().rev().fold(0u32, |acc, item| acc * 10 + *item);
    assert!(value == 321);
}

#[verify::test]
pub fn rev_fold_override() {
    let value = Odd { remaining: true }
        .rev()
        .fold(0u32, |acc, item| acc + item);
    assert!(value == 99);
}

fn fold_generic<I: Iterator<Item = u32>>(iter: I) -> u32 {
    iter.fold(0u32, |acc, item| acc + item)
}

#[verify::test]
pub fn rev_fold_generic_override() {
    assert!(fold_generic(Odd { remaining: true }.rev()) == 99);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rfold_cases() {
        rfold_slice();
        rfold_slice_last();
        rev_fold_slice();
        rev_fold_override();
        rev_fold_generic_override();
    }
}
