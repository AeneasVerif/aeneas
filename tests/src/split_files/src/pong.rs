//! The other half of the cross-file cycle with `ping`.

pub fn is_odd(n: u32) -> bool {
    if n == 0 { false } else { crate::ping::is_even(n - 1) }
}
