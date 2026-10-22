//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

fn test_unwrap_or<T>(x: Option<T>, default: T) -> T {
    x.unwrap_or(default)
}

fn test_expect<T>(x: Option<T>, msg: &str) -> T {
    x.expect(msg)
}

fn test_is_some<T>(x: Option<T>) -> bool {
    x.is_some()
}

// ---------------------------------------------------------------------------
// exercises Option::map on some and none, and with a closure that captures a value
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_map_some() {
    assert!(Some(1u32).map(|x| x + 1).unwrap() == 2);
}

/// on none, map must not call the closure, which panics
#[verify::test]
pub fn test_map_none() {
    let x: Option<u32> = None;
    assert!(x.map(|_| -> u32 { panic!() }).is_none());
}

/// the closure captures k, so unlike in the tests above its state is not empty and map must pass it to call_once
#[verify::test]
pub fn test_map_capture() {
    let k = 3u32;
    assert!(Some(1u32).map(|x| x + k).unwrap() == 4);
}

// ---------------------------------------------------------------------------
// exercises Option::is_some_and, true only if the option is some and the closure returns true
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_is_some_and_true() {
    assert!(Some(2u32).is_some_and(|x| x > 1));
}

#[verify::test]
pub fn test_is_some_and_false() {
    assert!(!Some(0u32).is_some_and(|x| x > 1));
}

/// on none, is_some_and must not call the closure, which panics
#[verify::test]
pub fn test_is_some_and_none() {
    let x: Option<u32> = None;
    assert!(!x.is_some_and(|_| panic!()));
}

// ---------------------------------------------------------------------------
// exercises bool::then, some of the closure's value if true, none if false
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_bool_then_true() {
    assert!(true.then(|| 1u32).unwrap() == 1);
}

/// on false, then must not call the closure, which panics
#[verify::test]
pub fn test_bool_then_false() {
    assert!(false.then(|| -> u32 { panic!() }).is_none());
}

// ---------------------------------------------------------------------------
// exercises Result::unwrap_or, through ok_if_even: the translation of an annotated Ok(2) drops the error type, which Lean then cannot infer
// ---------------------------------------------------------------------------

fn ok_if_even(x: u32) -> Result<u32, u32> {
    if x % 2 == 0 {
        Ok(x)
    } else {
        Err(x)
    }
}

#[verify::test]
pub fn test_result_unwrap_or_ok() {
    assert!(ok_if_even(2).unwrap_or(0) == 2);
}

#[verify::test]
pub fn test_result_unwrap_or_err() {
    assert!(ok_if_even(3).unwrap_or(0) == 0);
}
