//@ [!lean] skip
//@ [lean] subdir=ExtraIncludes
//@ [lean] aeneas-args=-split-files -extra-includes=Lean,Aeneas.Std.Alloc
//! Exercise the `-extra-includes` option: the modules it lists must be imported
//! at the top of *every* generated file.

pub struct Pair {
    pub x: u32,
    pub y: u32,
}

pub fn sum(p: Pair) -> u32 {
    p.x.wrapping_add(p.y)
}
