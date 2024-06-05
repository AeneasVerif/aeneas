//@ [!borrow-check] skip

fn iter_local_mut_borrow() {
    let mut x = 0;
    let mut p = &mut x;
    loop {
        p = &mut (*p);
        *p += 1;
    }
}
