//@ [!borrow-check] aeneas-args=-test-trans-units
//@ [coq,fstar] subdir=misc
//! The examples from the ICFP 2022 submission, all in one place.

// 2.1
pub fn ref_incr(x: &mut i32) {
    *x = *x + 1;
}

pub fn test_incr() {
    let mut x = 0i32;
    ref_incr(&mut x);
    assert!(x == 1);
}

// 2.2
pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        return x;
    } else {
        return y;
    }
}

pub fn test_choose() {
    let mut x = 0;
    let mut y = 0;
    let z = choose(true, &mut x, &mut y);
    *z = *z + 1;
    assert!(*z == 1);
    assert!(x == 1);
    assert!(y == 0);
}

// 2.3

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}
use List::Cons;
use List::Nil;

pub fn list_nth_mut<'a, T>(l: &'a mut List<T>, i: u32) -> &'a mut T {
    match l {
        Nil => {
            panic!()
        }
        Cons(x, tl) => {
            if i == 0 {
                return x;
            } else {
                return list_nth_mut(tl, i - 1);
            }
        }
    }
}

pub fn sum(l: &List<i32>) -> i32 {
    match l {
        Nil => {
            return 0;
        }
        Cons(x, tl) => {
            return *x + sum(tl);
        }
    }
}

pub fn test_nth() {
    let mut l = Cons(1, Box::new(Cons(2, Box::new(Cons(3, Box::new(Nil))))));
    let x = list_nth_mut(&mut l, 2);
    *x = *x + 1;
    assert!(sum(&l) == 7);
}

// 4.3
pub fn call_choose(mut p: (u32, u32)) -> u32 {
    let px = &mut p.0;
    let py = &mut p.1;
    let pz = choose(true, px, py);
    *pz = *pz + 1;
    return p.0;
}
