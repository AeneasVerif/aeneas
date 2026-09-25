//@ [!lean] skip
//@ charon-args=--targets x86_64-apple-darwin,aarch64-apple-darwin
//@ aeneas-args=-feature-gates
//! Tests the `-feature-gates` option: the functions annotated with
//! `#[target_feature(enable = "...")]` must start with an assertion checking
//! that the required features are available.
//!
//! We pin the targets so that the feature names below are valid whatever the
//! machine on which the tests are run.
#![allow(unused)]

#[cfg(target_arch = "x86_64")]
mod x86 {
    /// A single feature: we should introduce one assertion.
    #[target_feature(enable = "avx2")]
    pub unsafe fn add(x: u32, y: u32) -> u32 {
        x.wrapping_add(y)
    }

    /// Several features: one assertion per feature, in order.
    #[target_feature(enable = "sse2", enable = "avx2")]
    pub unsafe fn add_twice(x: u32, y: u32) -> u32 {
        x.wrapping_add(y).wrapping_add(y)
    }

    /// Calling a gated function from another gated function.
    #[target_feature(enable = "avx2")]
    pub unsafe fn call_add(x: u32, y: u32) -> u32 {
        add(x, y)
    }

    /// The assertions must be introduced in the function itself, not in the
    /// auxiliary functions generated for the loops.
    #[target_feature(enable = "avx2")]
    pub unsafe fn sum(x: &[u32]) -> u32 {
        let mut sum = 0u32;
        let mut i = 0;
        while i < x.len() {
            sum = sum.wrapping_add(x[i]);
            i += 1;
        }
        sum
    }
}

#[cfg(target_arch = "aarch64")]
mod arm {
    #[target_feature(enable = "neon")]
    pub unsafe fn add(x: u32, y: u32) -> u32 {
        x.wrapping_add(y)
    }
}

/// No feature: we shouldn't introduce any assertion.
pub fn add_plain(x: u32, y: u32) -> u32 {
    x.wrapping_add(y)
}

/// A multi-target dispatch which calls the gated functions.
pub fn dispatch_add(x: u32, y: u32) -> u32 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        x86::add(x, y)
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        arm::add(x, y)
    }
}
