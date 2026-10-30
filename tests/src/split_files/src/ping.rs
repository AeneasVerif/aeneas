//! Mutually recursive with `pong` across modules: the two modules form a cycle
//! in the dependency graph, so they are merged into a single Lean module.

pub fn is_even(n: u32) -> bool {
    if n == 0 { true } else { crate::pong::is_odd(n - 1) }
}
