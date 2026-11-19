//@ [lean] known-failure
//@ [!lean] skip
//@ [lean] aeneas-args=-external-names tests/external-names/external-names-duplicate-shipped.json
//! Checks that a file cannot map a pattern which a model shipped with Aeneas
//! already maps (`core::mem::swap`): a pattern may be mapped only once.

pub fn f(x: &mut u32, y: &mut u32) {
    core::mem::swap(x, y)
}
