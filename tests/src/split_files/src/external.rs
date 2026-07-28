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
