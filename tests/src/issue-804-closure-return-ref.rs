//@ [!lean] skip
//! Regression test for https://github.com/AeneasVerif/aeneas/issues/804
//! Closures that return references derived from their captured state.

pub fn each_ref(s: &[u8; 10]) -> [&u8; 10] {
    std::array::from_fn(|i| &s[i])
}
