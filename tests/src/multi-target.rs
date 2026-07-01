//@ [!lean] skip
//@ charon-args=--targets x86_64-apple-darwin,aarch64-apple-darwin
//@ charon-args=--sysroot=miri
#![allow(unused, non_camel_case_types)]

trait SimdTrait {
    type Vec: Copy;
    fn add(a: Self::Vec, b: Self::Vec) -> Self::Vec;
}

#[cfg(target_arch = "x86_64")]
mod x86 {
    use super::SimdTrait;

    pub struct Sse2;

    impl SimdTrait for Sse2 {
        type Vec = u128;

        fn add(a: u128, b: u128) -> u128 {
            a.wrapping_add(b)
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod arm {
    use super::SimdTrait;

    pub struct Neon;

    impl SimdTrait for Neon {
        type Vec = u128;

        fn add(a: u128, b: u128) -> u128 {
            a.wrapping_add(b)
        }
    }
}

fn add_vec<T: SimdTrait>(a: T::Vec, b: T::Vec) -> T::Vec {
    T::add(a, b)
}

fn scalar_add(a: u128, b: u128) -> u128 {
    a.wrapping_add(b)
}

fn cpu_features_present(_mask: u32) -> bool {
    true
}

fn dispatch_add(a: u128, b: u128) -> u128 {
    #[cfg(target_arch = "x86_64")]
    {
        if cpu_features_present(1) {
            add_vec::<x86::Sse2>(a, b)
        } else {
            scalar_add(a, b)
        }
    }

    #[cfg(target_arch = "aarch64")]
    {
        if cpu_features_present(2) {
            add_vec::<arm::Neon>(a, b)
        } else {
            scalar_add(a, b)
        }
    }
}

#[cfg(target_arch = "x86_64")]
pub struct Foo {
    pub data: [u16; 8],
}

#[cfg(target_arch = "aarch64")]
pub struct Foo {
    pub data: [u16; 4],
}

impl Foo {
    fn f(&self) {}
}
