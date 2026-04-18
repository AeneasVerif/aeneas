//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `Option` methods, verifying the Aeneas models match Rust behavior.
//!
//! Each test is the Rust docs example (adapted when a dependency is not yet
//! modelled; the adaptation is noted per test).

/// `Option::as_ref` — converts `&Option<T>` to `Option<&T>`.
/// Docs example uses `String::to_string`, `Option::map`, and `String::len`
/// none of which are modelled yet. This adapted test exercises the same
/// semantic (`as_ref` is an identity on the Option structure since
/// Aeneas erases references).
#[verify::test]
pub fn test_option_as_ref_some() {
    let x: Option<u32> = Some(97);
    let y = x.as_ref();
    match y {
        Some(&v) => assert!(v == 97),
        None => panic!(),
    }
}

fn make_none_u32() -> Option<u32> { None }

#[verify::test]
pub fn test_option_as_ref_none() {
    let x: Option<u32> = make_none_u32();
    let y: Option<&u32> = x.as_ref();
    match y {
        Some(_) => panic!(),
        None => (),
    }
}

/// `Option::ok_or` — verbatim from docs with the `assert_eq!` replaced by
/// pattern match since we lack `PartialEq for Result`.
///
/// Docs version:
/// ```rust
/// let x = Some("foo");
/// assert_eq!(x.ok_or(0), Ok("foo"));
///
/// let x: Option<&str> = None;
/// assert_eq!(x.ok_or(0), Err(0));
/// ```
#[verify::test]
pub fn test_option_ok_or_some() {
    let x: Option<u32> = Some(42);
    match x.ok_or(0u32) {
        Ok(v) => assert!(v == 42),
        Err(_) => panic!(),
    }
}

#[verify::test]
pub fn test_option_ok_or_none() {
    let x: Option<u32> = make_none_u32();
    let r: Result<u32, u32> = x.ok_or(7);
    match r {
        Ok(_) => panic!(),
        Err(e) => assert!(e == 7),
    }
}

/// `Option::Default::default()` — verbatim from docs.
///
/// ```rust
/// let opt: Option<u32> = Option::default();
/// assert!(opt.is_none());
/// ```
#[verify::test]
pub fn test_option_default() {
    let opt: Option<u32> = Option::default();
    assert!(opt.is_none());
}

/// `PartialEq for Option<T>::eq` — verbatim from docs.
///
/// ```rust
/// let x = Some(2);
/// let y = Some(2);
/// assert_eq!(x == y, true);
///
/// let x = Some(2);
/// let y = Some(3);
/// assert_eq!(x == y, false);
///
/// let x: Option<u32> = None;
/// let y = Some(2);
/// assert_eq!(x == y, false);
/// ```
#[verify::test]
pub fn test_option_partial_eq_some_some_eq() {
    let x: Option<u32> = Some(2);
    let y: Option<u32> = Some(2);
    assert!((x == y) == true);
}

#[verify::test]
pub fn test_option_partial_eq_some_some_neq() {
    let x: Option<u32> = Some(2);
    let y: Option<u32> = Some(3);
    assert!((x == y) == false);
}

#[verify::test]
pub fn test_option_partial_eq_none_some() {
    let x: Option<u32> = make_none_u32();
    let y: Option<u32> = Some(2);
    assert!((x == y) == false);
}

/// `Clone for Option<T>::clone` — the docs don't show a verbatim clone
/// example (they show `cloned()` which is a different method). This test
/// exercises the clone trait impl directly.
#[verify::test]
pub fn test_option_clone_some() {
    let x: Option<u32> = Some(5);
    let y = x.clone();
    match y {
        Some(v) => assert!(v == 5),
        None => panic!(),
    }
}

#[verify::test]
pub fn test_option_clone_none() {
    let x: Option<u32> = make_none_u32();
    let y = x.clone();
    assert!(y.is_none());
}
