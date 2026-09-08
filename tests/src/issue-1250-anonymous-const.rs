//@ [!lean] skip

//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1250
//!
//! Anonymous constants (`const _`) are permitted in Rust. However, without
//! escaping `_` isn't a valid Lean identifier. Moreover `_` is not an
//! identifier in Rust and so can appear multiple times.

const _: () = ();
const _: () = ();
