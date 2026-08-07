//! Checks the external declaration bucket output under `-split-files`.
//!
//! `Sink` implements the external, non-builtin trait `core::fmt::Write`.
//! It lands in a `FunsExternal` module.

use core::fmt::Write;

pub struct Sink;

impl core::fmt::Write for Sink {
    fn write_str(&mut self, _s: &str) -> core::fmt::Result {
        Ok(())
    }
}

pub fn emit(s: &mut Sink) -> core::fmt::Result {
    s.write_str("hi")
}

/// `macrolib::helper` has no translated body, so it lands in the same external
/// bucket as the (transparent) `Write` trait decl above, as an axiom. The
/// bucket therefore mixes opacities and must still come out as a single
/// `FunsExternal_Template` file, never a `Part`/`Axioms` chain.
pub fn use_helper(x: u32) -> u32 {
    macrolib::helper(x)
}
