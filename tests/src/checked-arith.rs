//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/1257
//! Charon emits MIR's `CheckedBinaryOp` as `AddChecked`/`SubChecked`/
//! `MulChecked` when it can't fold the binop together with its companion
//! `Assert(Overflow)` back into a single panicking operation. Those used to
//! abort translation, in the interpreter and then in the Lean backend.
//!
//! Here the assignment's left-hand side is a place MIR has to compute first,
//! which introduces an extra copy between the two statements, so the fold no
//! longer applies.

pub fn add_checked(output: u32, a: &mut u8, b: &mut u8, c: bool) {
    *(if c { a } else { b }) = b'0' + output as u8;
}

pub fn sub_checked(output: u32, a: &mut u8, b: &mut u8, c: bool) {
    *(if c { a } else { b }) = output as u8 - b'0';
}

pub fn mul_checked(output: u32, a: &mut u8, b: &mut u8, c: bool) {
    *(if c { a } else { b }) = output as u8 * 10;
}
