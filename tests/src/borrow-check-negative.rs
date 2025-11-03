//@ charon-args=--skip-borrowck
//@ [!borrow-check] skip
//@ [borrow-check] known-failure
//@ [borrow-check] aeneas-args=-log-error MainLogger
// Some negative tests for borrow checking

// This succeeds
fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        x
    } else {
        y
    }
}

pub fn choose_test() {
    let mut x = 0;
    let mut y = 0;
    let z = choose(true, &mut x, &mut y);
    *z += 1;
    assert!(*z == 1);
    // drop(z)
    assert!(x == 1);
    assert!(y == 0);
    assert!(*z == 1); // z is not valid anymore
}

fn choose_wrong<'a, 'b, T>(b: bool, x: &'a mut T, y: &'b mut T) -> &'a mut T {
    if b {
        x
    } else {
        y // Expected lifetime 'a
    }
}

fn test_mut1(b: bool) {
    let mut x = 0;
    let mut y = 1;
    let z = if b { &mut x } else { &mut y };
    *z += 1;
    assert!(x >= 0);
    *z += 1; // z is not valid anymore
}

#[allow(unused_assignments)]
fn test_mut2(b: bool) {
    let mut x = 0;
    let mut y = 1;
    let z = if b { &x } else { &y };
    x += 1;
    assert!(*z == 0); // z is not valid anymore
}

fn test_move1<T>(x: T) -> T {
    let _ = x;
    return x; // x has been moved
}

pub fn refs_test1() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    **ppx = 1;
    assert!(x == 1);
    assert!(**ppx == 1); // ppx has ended
}

pub fn refs_test2() {
    let mut x = 0;
    let mut y = 1;
    let mut px = &mut x;
    let py = &mut y;
    let ppx = &mut px;
    *ppx = py;
    **ppx = 2;
    assert!(*px == 2);
    assert!(x == 0);
    assert!(*py == 2);
    assert!(y == 2);
    assert!(**ppx == 2); // ppx has ended
}

pub fn test_box1() {
    use std::ops::Deref;
    use std::ops::DerefMut;
    let mut b: Box<i32> = Box::new(0);
    let x0 = b.deref_mut();
    *x0 = 1;
    let x1 = b.deref();
    assert!(*x1 == 1);
    assert!(*x0 == 1); // x0 has ended
}
