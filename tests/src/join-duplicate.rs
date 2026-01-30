//@ [!lean] skip

fn join_nested_shared(b : bool) {
    let x = 1;
    let y = 2;
    let px = &x;
    let py = &y;
    let p = if b { &px } else { &py };
    assert!(**p > 0);
}
