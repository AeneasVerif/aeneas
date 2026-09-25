//@ [!lean] skip

fn join_nested_shared(b: bool) {
    let x = 1;
    let y = 2;
    let px = &x;
    let py = &y;
    let p = if b { &px } else { &py };
    assert!(**p > 0);
}

// Regression test.
//
// A nested shared borrow (`p: &&i32`) is kept alive across a loop. The loop
// fixed-point computation thus has to join two contexts which both contain a
// shared loan whose shared value is itself a shared borrow. As long as the
// loan ids match on both sides, this join is well-defined (we simply keep the
// shared loan), and should not be rejected.
fn join_nested_shared_in_loop(b: bool, n: u32) -> i32 {
    let x = 1;
    let y = 2;
    let px = &x;
    let py = &y;
    let p = if b { &px } else { &py };
    let mut i = 0;
    while i < n {
        i += 1;
    }
    **p
}
