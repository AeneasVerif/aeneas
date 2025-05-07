//@ [coq,fstar] aeneas-args=-use-fuel
//@ [coq,fstar] subdir=demo
//@ [lean] subdir=Demo
#![allow(clippy::needless_lifetimes)]

/* Simple functions */

pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        x
    } else {
        y
    }
}

pub fn mul2_add1(x: u32) -> u32 {
    (x + x) + 1
}

pub fn use_mul2_add1(x: u32, y: u32) -> u32 {
    mul2_add1(x) + y
}

pub fn incr<'a>(x: &'a mut u32) {
    *x += 1;
}

pub fn use_incr() {
    let mut x = 0;
    incr(&mut x);
    incr(&mut x);
    incr(&mut x);
}

/* Recursion, loops */

pub enum CList<T> {
    CCons(T, Box<CList<T>>),
    CNil,
}

pub fn list_nth<'a, T>(l: &'a CList<T>, i: u32) -> &'a T {
    match l {
        CList::CCons(x, tl) => {
            if i == 0 {
                x
            } else {
                list_nth(tl, i - 1)
            }
        }
        CList::CNil => {
            panic!()
        }
    }
}

pub fn list_nth1<'a, T>(mut l: &'a CList<T>, mut i: u32) -> &'a T {
    while let CList::CCons(x, tl) = l {
        if i == 0 {
            return x;
        }
        i -= 1;
        l = tl;
    }
    panic!()
}

pub fn list_nth_mut<'a, T>(mut l: &'a mut CList<T>, mut i: u32) -> &'a mut T {
    match l {
        CList::CCons(x, tl) => {
            if i == 0 {
                x
            } else {
                list_nth_mut(tl, i - 1)
            }
        }
        CList::CNil => {
            panic!()
        }
    }
}

pub fn i32_id(i: i32) -> i32 {
    if i == 0 {
        0
    } else {
        i32_id(i - 1) + 1
    }
}

pub fn list_tail<'a, T>(l: &'a mut CList<T>) -> &'a mut CList<T> {
    match l {
        CList::CCons(_, tl) => list_tail(tl),
        CList::CNil => l,
    }
}

/* Traits */

pub trait Counter {
    fn incr(&mut self) -> usize;
}

impl Counter for usize {
    fn incr(&mut self) -> usize {
        let x = *self;
        *self += 1;
        x
    }
}

pub fn use_counter<'a, T: Counter>(cnt: &'a mut T) -> usize {
    cnt.incr()
}

/* Cryptographic example */
fn mod_add(a: u32, b: u32) -> u32 {
    assert!(a < 3329);
    assert!(b < 3329);
    let sum = a + b; // 0 <= a + b <= 2 * 3329
    let res = sum.wrapping_sub(3329);
    let mask = res >> 16; // mask = 0xffff if a + b < 3329, mask = 0 otherwise
    let q = 3329 & mask; // q = 3329 if a + b < 3329, q = 0 otherwise
    res.wrapping_add(q)
}
