//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods
#![feature(register_tool)]
#![register_tool(verify)]

struct Countdown {
    remaining: u32,
}

impl Iterator for Countdown {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            None
        } else {
            let value = self.remaining;
            self.remaining -= 1;
            Some(value)
        }
    }
}

struct OneShot {
    value: Option<u32>,
}

impl Iterator for OneShot {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.value;
        self.value = None;
        value
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        match self.value {
            Some(value) => f(init, value),
            None => init,
        }
    }
}

#[verify::test]
pub fn fold_countdown() {
    let sum = Countdown { remaining: 3 }.fold(0u32, |acc, value| acc + value);
    assert!(sum == 6);
}

#[verify::test]
pub fn fold_empty() {
    let sum = Countdown { remaining: 0 }.fold(7u32, |acc, value| acc + value);
    assert!(sum == 7);
}

fn fold_values<I: Iterator<Item = u32>>(iter: I) -> u32 {
    iter.fold(0u32, |acc, value| acc + value)
}

#[verify::test]
pub fn fold_generic() {
    assert!(fold_values(Countdown { remaining: 3 }) == 6);
}

#[verify::test]
pub fn fold_override() {
    assert!(fold_values(OneShot { value: Some(5) }) == 5);
}

#[verify::test]
pub fn fold_stateful_closure() {
    let mut offset = 0u32;
    let sum = Countdown { remaining: 3 }.fold(0u32, move |acc, value| {
        offset += 1;
        acc + value + offset
    });
    assert!(sum == 12);
}

#[verify::test]
pub fn fold_slice() {
    let values = [1u32, 2, 3];
    let value = values.iter().fold(0u32, |acc, item| acc * 10 + *item);
    assert!(value == 123);
}
