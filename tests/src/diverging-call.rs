//@ [!lean] skip
//@ [lean] known-failure
// A call to a function returning `!` which ends the block (Charon emits no
// `undefined_behavior` after it) must be treated as diverging.
fn die() -> ! {
    panic!()
}

pub fn arm(x: Option<u32>) -> u32 {
    match x {
        Some(v) => v,
        None => die(),
    }
}

pub fn catch_all(x: Option<u32>) -> u32 {
    match x {
        Some(v) => v,
        _ => die(),
    }
}
