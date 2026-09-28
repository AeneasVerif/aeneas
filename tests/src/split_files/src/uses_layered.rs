//! Depends on `layered`, which contains an opaque declaration. Nothing here is
//! opaque, but `mystery` is an axiom in Lean, so the definitions below are not
//! computable either and this module still needs `noncomputable section`.
use crate::layered::double_mystery;

pub fn quadruple_mystery(x: i32) -> i32 {
    double_mystery(x) * 2
}
