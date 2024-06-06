//@ [!borrow-check] skip
//@ [borrow-check] known-failure

// We need to use the general rules for joining the loans
fn loop_reborrow_mut() {
    let mut x = 0;
    let mut px = &mut x;
    while *px > 0 {
        x += 1;
        px = &mut x;
    }
}

// We need to imrpove [prepare_ashared_loans]
fn iter_local_shared_borrow() {
    let mut x = 0;
    let mut p = &x;
    loop {
        p = &(*p);
    }
}
