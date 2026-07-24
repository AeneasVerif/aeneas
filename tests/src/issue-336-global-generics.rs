//@ [!lean] skip
//! Regression tests for issue #336: the generic parameters of
//! globals/constants are minimized to the parameters they actually use.

pub trait Tr {
    const LEN: usize;
}

pub struct S<const N: usize, T>([T; N]);

// Keeps `N`, drops `T`.
impl<const N: usize, T> S<N, T> {
    pub const LEN: usize = N;
}

// Drops everything: zero-parameter constant.
pub struct S2<T>(T);
impl<T> S2<T> {
    pub const ZERO: u32 = 0;
}

// `T` is used only in the constant's *type*: keeps `T` (which becomes
// explicit), drops `U` and the (unused) `Default` clause.
pub struct S3<T, U>(T, U);
impl<T: Default, U> S3<T, U> {
    pub const NONE: Option<T> = None;
}

// The `Tr` clause is used (`T::LEN`), which forces keeping `T`; `U` is
// dropped.
pub struct S4<T, U>(T, U);
impl<T: Tr, U> S4<T, U> {
    pub const D: usize = T::LEN;
}

// Defaulted associated constant in a generic trait: it uses nothing, so all
// the trait generics are dropped.
pub trait WithDefault<T> {
    const DFLT: usize = 7;
}

pub struct P;

impl Tr for P {
    const LEN: usize = 3;
}

impl WithDefault<u32> for P {}

// Use sites: generic and concrete reads of the constants.
pub fn use_len<const N: usize, T>() -> usize {
    S::<N, T>::LEN
}

pub fn use_all() -> usize {
    let _none = S3::<u8, u16>::NONE;
    S2::<u8>::ZERO as usize + S4::<P, u16>::D + <P as WithDefault<u32>>::DFLT
}
