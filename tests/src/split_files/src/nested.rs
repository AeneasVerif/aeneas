//! Inline modules are placed like the others. `inner` doesn't use `nested`, so
//! it gets its own Lean module, `Nested.Inner`. `cyclic` and `nested` use each
//! other, so they share one, named `Nested` after the module that contains the
//! other.

pub mod inner {
    pub fn one() -> u32 {
        1
    }
}

pub mod cyclic {
    pub fn down(n: u32) -> u32 {
        if n == 0 { 0 } else { super::up(n - 1) }
    }
}

pub fn up(n: u32) -> u32 {
    if n == 0 { inner::one() } else { cyclic::down(n - 1) }
}
