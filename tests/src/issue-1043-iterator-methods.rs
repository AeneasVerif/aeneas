//@ [!lean] skip

//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1043
//! `.enumerate().map(...).collect()` used to extract to an invalid `Iterator`
//! record (with `map`/`collect` fields that don't exist in the model, and
//! missing `step_by`/`take`).

pub fn indexed_squares<I: Iterator<Item = u32>>(iter: I) -> Vec<u32> {
    iter.enumerate().map(|(i, x)| x + i as u32).collect()
}

pub fn call_it(n: u32) -> Vec<u32> {
    indexed_squares(0..n)
}
