//@ [!lean] skip
// Issue #815: globals referencing fallible globals should also be fallible

const INNER: u32 = 1 + 1;
pub const OUTER: u32 = INNER;
