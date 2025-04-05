//@ [!lean] skip

fn test_unwrap_or<T>(x: Option<T>, default: T) -> T {
    x.unwrap_or(default)
}
