//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for `Result` methods, verifying the Aeneas models match Rust behavior.

fn make_err_u32(e: u32) -> Result<u32, u32> {
    Err(e)
}
fn make_ok_u32(v: u32) -> Result<u32, u32> {
    Ok(v)
}

/// `Result::is_ok` — adapted from docs. Docs example uses `&str` error which
/// isn't modelled yet; this test uses `u32` error and otherwise matches.
///
/// ```rust
/// let x: Result<i32, &str> = Ok(-3);
/// assert_eq!(x.is_ok(), true);
///
/// let x: Result<i32, &str> = Err("Some error message");
/// assert_eq!(x.is_ok(), false);
/// ```
#[verify::test]
pub fn test_result_is_ok_ok() {
    let x: Result<u32, u32> = make_ok_u32(97);
    assert!(x.is_ok() == true);
}

#[verify::test]
pub fn test_result_is_ok_err() {
    let x: Result<u32, u32> = make_err_u32(1);
    assert!(x.is_ok() == false);
}

/// `Result::unwrap_or` — adapted from docs: `u32` error instead of `&str`.
///
/// ```rust
/// let default = 2;
/// let x: Result<u32, &str> = Ok(9);
/// assert_eq!(x.unwrap_or(default), 9);
///
/// let x: Result<u32, &str> = Err("error");
/// assert_eq!(x.unwrap_or(default), default);
/// ```
#[verify::test]
pub fn test_result_unwrap_or_ok() {
    let default: u32 = 2;
    let x: Result<u32, u32> = make_ok_u32(9);
    assert!(x.unwrap_or(default) == 9);
}

#[verify::test]
pub fn test_result_unwrap_or_err() {
    let default: u32 = 2;
    let x: Result<u32, u32> = make_err_u32(7);
    assert!(x.unwrap_or(default) == default);
}

/// `Result::map` — heavily adapted. Docs example uses `str::lines`, `str::parse`,
/// `println!` — none modelled. This test exercises `map` with a pure closure on
/// integer success values.
#[verify::test]
pub fn test_result_map_ok() {
    let x: Result<u32, u32> = make_ok_u32(5);
    let y: Result<u32, u32> = x.map(|i| i * 2);
    match y {
        Ok(v) => assert!(v == 10),
        Err(_) => panic!(),
    }
}

#[verify::test]
pub fn test_result_map_err_passthrough() {
    let x: Result<u32, u32> = make_err_u32(3);
    let y: Result<u32, u32> = x.map(|i| i * 2);
    match y {
        Ok(_) => panic!(),
        Err(e) => assert!(e == 3),
    }
}

/// `Result::map_err` — heavily adapted. Docs example uses `String::from`,
/// `format!` — neither modelled. Pure-closure version here.
#[verify::test]
pub fn test_result_map_err_ok_passthrough() {
    let x: Result<u32, u32> = make_ok_u32(2);
    let y: Result<u32, u32> = x.map_err(|e| e + 100);
    match y {
        Ok(v) => assert!(v == 2),
        Err(_) => panic!(),
    }
}

#[verify::test]
pub fn test_result_map_err_err() {
    let x: Result<u32, u32> = make_err_u32(13);
    let y: Result<u32, u32> = x.map_err(|e| e + 100);
    match y {
        Ok(_) => panic!(),
        Err(e) => assert!(e == 113),
    }
}

/// `Try::branch` for `Result<T, E>` — exercised implicitly via the `?` operator
/// in any function that propagates errors. Pure test of the behavior:
/// `?` on `Ok(v)` evaluates to `v`; `?` on `Err(e)` returns early with `Err(e)`.
fn try_branch_helper(x: Result<u32, u32>) -> Result<u32, u32> {
    let v = x?;
    Ok(v + 1)
}

#[verify::test]
pub fn test_result_try_branch_ok() {
    match try_branch_helper(Ok(10)) {
        Ok(v) => assert!(v == 11),
        Err(_) => panic!(),
    }
}

#[verify::test]
pub fn test_result_try_branch_err() {
    match try_branch_helper(make_err_u32(99)) {
        Ok(_) => panic!(),
        Err(e) => assert!(e == 99),
    }
}
