//@ [!lean] skip

fn test_unwrap_or<T>(x: Option<T>, default: T) -> T {
    x.unwrap_or(default)
}

fn test_expect<T>(x: Option<T>, msg: &str) -> T {
    x.expect(msg)
}
