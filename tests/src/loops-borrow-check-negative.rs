//@ charon-args=--skip-borrowck
//@ [!borrow-check] skip
//@ [borrow-check] known-failure
//@ [borrow-check] aeneas-args=-log-error MainLogger

// This succeeds
fn loop_a<'a>(a: &'a mut u32, b: &'a mut u32) -> &'a mut u32 {
    let mut x = 0;
    while x > 0 {
        x += 1;
    }
    if x > 0 {
        a
    } else {
        b
    }
}

// This fails
fn loop_a_b<'a, 'b>(a: &'a mut u32, b: &'b mut u32) -> &'a mut u32 {
    let mut x = 0;
    while x > 0 {
        x += 1;
    }
    if x > 0 {
        a
    } else {
        b // Expect lifetime 'a
    }
}
