//@ [!lean] skip
//! Regression test: comparison operators ([<], [<=], [>=], [>]) applied to
//! booleans.

pub fn le(a: bool, b: bool) -> bool {
    a <= b
}

pub fn lt(a: bool, b: bool) -> bool {
    a < b
}

pub fn ge(a: bool, b: bool) -> bool {
    a >= b
}

pub fn gt(a: bool, b: bool) -> bool {
    a > b
}
