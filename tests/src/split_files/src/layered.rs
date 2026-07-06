//! Alternates transparent and opaque declarations: the module splits into a
//! chain of regenerated `PartK` files and user-fillable `AxiomsK` templates,
//! plus an imports-only aggregator.

pub fn double(x: i32) -> i32 {
    x * 2
}

/// Extracted as an axiom into a template file.
#[verify::opaque]
pub fn mystery(x: i32) -> i32 {
    x + 1
}

pub fn double_mystery(x: i32) -> i32 {
    double(mystery(x))
}
