//@ [!lean] skip
//@ [lean] subdir=ExtraIncludes
//@ [lean] aeneas-args=-split-files -extra-includes=ExtraIncludesModel
//! Exercise the `-extra-includes` option: the modules it lists (here, the
//! hand-written `tests/lean/ExtraIncludesModel.lean`) must be imported
//! at the top of *every* generated file.

pub struct S;

pub fn f(x: S) -> S {
    x
}
