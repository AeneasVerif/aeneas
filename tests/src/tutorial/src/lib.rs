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

pub fn mul2_add1_add(x: u32, y: u32) -> u32 {
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

pub fn list_nth_mut<'a, T>(l: &'a mut CList<T>, i: u32) -> &'a mut T {
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

pub fn i32_id(i : i32) -> i32 {
    if i == 0 {
        0
    }
    else {
        i32_id(i - 1) + 1
    }
}

pub fn even(i : u32) -> bool {
    if i == 0 {
        true
    }
    else {
        odd(i - 1)
    }
}

pub fn odd(i : u32) -> bool {
    if i == 0 {
        false
    }
    else {
        even(i - 1)
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

/* Exercises: warm up */

pub fn list_nth_mut1<'a, T>(mut l: &'a mut CList<T>, mut i: u32) -> &'a mut T {
    while let CList::CCons(x, tl) = l {
        if i == 0 {
            return x;
        }
        i -= 1;
        l = tl;
    }
    panic!()
}

pub fn list_tail<'a, T>(mut l: &'a mut CList<T>) -> &'a mut CList<T> {
    while let CList::CCons(_, tl) = l {
        l = tl;
    }
    l
}

pub fn append_in_place<'a, T>(l0: &'a mut CList<T>,  l1 : CList<T>) {
    let tl = list_tail(l0);
    *tl = l1;
}

pub fn reverse<T>(mut l : CList<T>) -> CList<T> {
    let mut out = CList::CNil;
    while let CList::CCons(hd, mut tl) = l {
        l = *tl;
        *tl = out;
        out = CList::CCons(hd, tl);
    }
    out
}


/* Big numbers */

pub type Bignum = Vec<u32>;

/// Zero out a bignum
pub fn zero(x : &mut Bignum) {
    let mut i = 0;
    while i < x.len() {
        x[i] = 0;
        i += 1;
    }
}

/// Add a bignum in place.
///
/// We assume that:
/// - they have the same length
/// - there is no overflow when suming the individual thunks
pub fn add_no_overflow(x: &mut Bignum, y: &Bignum) {
    let mut i = 0;
    while i < x.len() {
        x[i] += y[i]; // We assume this doesn't overflow
        i += 1;
    }
}

/// Add a bignum in place, and return the carry.
///
/// We assume the bignums have the same length
pub fn add_with_carry(x: &mut Bignum, y: &Bignum) -> u8 {
    let mut c0 = 0u8;
    let mut i = 0;
    // Remark: we have (and need) the invariant that: c0 <= 1
    while i < x.len() {
        let (sum, c1) = x[i].overflowing_add(c0 as u32);
        let (sum, c2) = sum.overflowing_add(y[i]);
        // We have: c1 as u8 + c2 as u8 <= 1
        c0 = (c1 as u8 + c2 as u8) as u8;
        x[i] = sum;
        i += 1;
    }
    c0
}

fn max(x : usize, y : usize) -> usize {
    if x > y { x } else { y }
}

fn get_or_zero(y : &Bignum, i : usize) -> u32 {
    if i < y.len() { y[i] } else { 0 }
}

/// Add a bignum in place.
///
/// The bignums may have different lengths, and we resize x if necessary.
/// Note: this is not what we usually do in cryptographic code, where big
/// numbers have a fixed size, but is interesting as an exercise.
pub fn add(x: &mut Bignum, y: &Bignum) {
    let max = max(x.len(), y.len());
    x.resize(max, 0u32);
    // now: length x >= length y
    let mut c0 = 0u8;
    let mut i = 0;
    // Remark: we have (and need) the invariant that: c0 <= 1
    while i < max {
        let yi = get_or_zero(y, i);
        let (sum, c1) = x[i].overflowing_add(c0 as u32);
        let (sum, c2) = sum.overflowing_add(yi);
        // We have: c1 as u8 + c2 as u8 <= 1
        c0 = (c1 as u8 + c2 as u8) as u8;
        x[i] = sum;
        i += 1;
    }

    // Resize x again if the carry is != 0
    if c0 != 0 {
        x.push(c0 as u32)
    }
}

#[test]
fn test() {
    // TODO:
    // let mut x = vec![0xffffffffu32];
    // let mut y = vec![0xffffffffu32];
    let mut x = Vec::from([0xffffffffu32]);
    let mut y = Vec::from([0xffffffffu32]);
    let carry = add_with_carry(&mut x, &mut y);
    assert!(carry == 1);
    assert!(x.len() == 1);
    assert!(x[0] == 0xfffffffe);
}
