//@ [!lean] skip
// `?` on a `Result` whose error type lives in a `max` universe.

pub fn pair_err<T, E1, E2>(r: Result<T, (E1, E2)>) -> Result<T, (E1, E2)> {
    let x = r?;
    Ok(x)
}
