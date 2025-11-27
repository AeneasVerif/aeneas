//@ [!lean] skip
use std::vec::Vec;

pub fn iter(max: u32) -> u32 {
    let mut i = 0;
    while i < max {
        i += 1;
    }

    i
}

/// No borrows
pub fn sum(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        s += i;
        i += 1;
    }

    s *= 2;
    s
}

/// Same as [sum], but we use borrows in order tocreate loans inside a loop
/// iteration, and those borrows will have to be ended by the end of the
/// iteration.
pub fn sum_with_mut_borrows(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        let ms = &mut s;
        *ms += i;
        let mi = &mut i;
        *mi += 1;
    }

    s *= 2;
    s
}

/// Similar to [sum_with_mut_borrows].
pub fn sum_with_shared_borrows(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        i += 1;
        // We changed the order compared to [sum_with_mut_borrows]:
        // we want to have a shared borrow surviving until the end
        // of the iteration.
        let mi = &i;
        s += *mi;
    }

    s *= 2;
    s
}

pub fn sum_array<const N: usize>(a: [u32; N]) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < N {
        s += a[i];
        i += 1;
    }
    s
}

/// This case is interesting, because the fixed point for the loop doesn't
/// introduce new abstractions.
pub fn clear(v: &mut Vec<u32>) {
    let mut i = 0;
    while i < v.len() {
        v[i] = 0;
        i += 1;
    }
}

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// The parameter `x` is a borrow on purpose
pub fn list_mem(x: &u32, mut ls: &List<u32>) -> bool {
    while let List::Cons(y, tl) = ls {
        if *y == *x {
            return true;
        } else {
            ls = tl;
        }
    }
    false
}

pub fn list_nth_mut<T>(mut ls: &mut List<T>, mut i: u32) -> &mut T {
    while let List::Cons(x, tl) = ls {
        if i == 0 {
            return x;
        } else {
            ls = tl;
            i -= 1;
        }
    }
    panic!()
}

/// Same as [list_nth_mut] but with shared borrows
pub fn list_nth_shared<T>(mut ls: &List<T>, mut i: u32) -> &T {
    while let List::Cons(x, tl) = ls {
        if i == 0 {
            return x;
        } else {
            ls = tl;
            i -= 1;
        }
    }
    panic!()
}

pub fn get_elem_mut(slots: &mut Vec<List<usize>>, x: usize) -> &mut usize {
    let mut ls = &mut slots[0];
    loop {
        match ls {
            List::Nil => panic!(),
            List::Cons(y, tl) => {
                if *y == x {
                    return y;
                } else {
                    ls = tl;
                }
            }
        }
    }
}

pub fn get_elem_shared(slots: &Vec<List<usize>>, x: usize) -> &usize {
    let mut ls = &slots[0];
    loop {
        match ls {
            List::Nil => panic!(),
            List::Cons(y, tl) => {
                if *y == x {
                    return y;
                } else {
                    ls = tl;
                }
            }
        }
    }
}

pub fn id_mut<T>(ls: &mut List<T>) -> &mut List<T> {
    ls
}

pub fn id_shared<T>(ls: &List<T>) -> &List<T> {
    ls
}

/// Small variation of [list_nth_mut]
pub fn list_nth_mut_with_id<T>(ls: &mut List<T>, mut i: u32) -> &mut T {
    let mut ls = id_mut(ls);
    while let List::Cons(x, tl) = ls {
        if i == 0 {
            return x;
        } else {
            ls = tl;
            i -= 1;
        }
    }
    panic!()
}

/// Small variation of [list_nth_shared]
pub fn list_nth_shared_with_id<T>(ls: &List<T>, mut i: u32) -> &T {
    let mut ls = id_shared(ls);
    while let List::Cons(x, tl) = ls {
        if i == 0 {
            return x;
        } else {
            ls = tl;
            i -= 1;
        }
    }
    panic!()
}

/// Same as [list_nth_mut] but on a pair of lists.
///
/// This test checks that we manage to decompose a loop into disjoint regions.
pub fn list_nth_mut_pair<'a, 'b, T>(
    mut ls0: &'a mut List<T>,
    mut ls1: &'b mut List<T>,
    mut i: u32,
) -> (&'a mut T, &'b mut T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Same as [list_nth_mut_pair] but with shared borrows.
pub fn list_nth_shared_pair<'a, 'b, T>(
    mut ls0: &'a List<T>,
    mut ls1: &'b List<T>,
    mut i: u32,
) -> (&'a T, &'b T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Same as [list_nth_mut_pair] but this time we force the two loop
/// regions to be merged.
pub fn list_nth_mut_pair_merge<'a, T>(
    mut ls0: &'a mut List<T>,
    mut ls1: &'a mut List<T>,
    mut i: u32,
) -> (&'a mut T, &'a mut T) {
    while let (List::Cons(x0, tl0), List::Cons(x1, tl1)) = (ls0, ls1) {
        if i == 0 {
            return (x0, x1);
        } else {
            ls0 = tl0;
            ls1 = tl1;
            i -= 1;
        }
    }
    panic!()
}

/// Same as [list_nth_mut_pair_merge] but with shared borrows.
pub fn list_nth_shared_pair_merge<'a, T>(
    mut ls0: &'a List<T>,
    mut ls1: &'a List<T>,
    mut i: u32,
) -> (&'a T, &'a T) {
    while let (List::Cons(x0, tl0), List::Cons(x1, tl1)) = (ls0, ls1) {
        if i == 0 {
            return (x0, x1);
        } else {
            ls0 = tl0;
            ls1 = tl1;
            i -= 1;
        }
    }
    panic!()
}

/// Mixing mutable and shared borrows.
pub fn list_nth_mut_shared_pair<'a, 'b, T>(
    mut ls0: &'a mut List<T>,
    mut ls1: &'b List<T>,
    mut i: u32,
) -> (&'a mut T, &'b T) {
    while let (List::Cons(x0, tl0), List::Cons(x1, tl1)) = (ls0, ls1) {
        if i == 0 {
            return (x0, x1);
        } else {
            ls0 = tl0;
            ls1 = tl1;
            i -= 1;
        }
    }
    panic!()
}

/// Same as [list_nth_mut_shared_pair] but this time we force the two loop
/// regions to be merged.
pub fn list_nth_mut_shared_pair_merge<'a, T>(
    mut ls0: &'a mut List<T>,
    mut ls1: &'a List<T>,
    mut i: u32,
) -> (&'a mut T, &'a T) {
    while let (List::Cons(x0, tl0), List::Cons(x1, tl1)) = (ls0, ls1) {
        if i == 0 {
            return (x0, x1);
        } else {
            ls0 = tl0;
            ls1 = tl1;
            i -= 1;
        }
    }
    panic!()
}

/// Same as [list_nth_mut_shared_pair], but we switched the positions of
/// the mutable and shared borrows.
pub fn list_nth_shared_mut_pair<'a, 'b, T>(
    mut ls0: &'a List<T>,
    mut ls1: &'b mut List<T>,
    mut i: u32,
) -> (&'a T, &'b mut T) {
    while let (List::Cons(x0, tl0), List::Cons(x1, tl1)) = (ls0, ls1) {
        if i == 0 {
            return (x0, x1);
        } else {
            ls0 = tl0;
            ls1 = tl1;
            i -= 1;
        }
    }
    panic!()
}

/// Same as [list_nth_mut_shared_pair_merge], but we switch the positions of
/// the mutable and shared borrows.
pub fn list_nth_shared_mut_pair_merge<'a, T>(
    mut ls0: &'a List<T>,
    mut ls1: &'a mut List<T>,
    mut i: u32,
) -> (&'a T, &'a mut T) {
    while let (List::Cons(x0, tl0), List::Cons(x1, tl1)) = (ls0, ls1) {
        if i == 0 {
            return (x0, x1);
        } else {
            ls0 = tl0;
            ls1 = tl1;
            i -= 1;
        }
    }
    panic!()
}

// We do not use the input borrow inside the loop
#[allow(clippy::empty)]
pub fn ignore_input_mut_borrow(_a: &mut u32, mut i: u32) {
    while i > 0 {
        i -= 1;
    }
}

// We do not use the input borrow inside the loop
#[allow(clippy::empty)]
pub fn incr_ignore_input_mut_borrow(a: &mut u32, mut i: u32) {
    *a += 1;
    while i > 0 {
        i -= 1;
    }
}

// We do not use the input borrow inside the loop
#[allow(clippy::empty)]
pub fn ignore_input_shared_borrow(_a: &mut u32, mut i: u32) {
    while i > 0 {
        i -= 1;
    }
}

/// Comes from: https://github.com/AeneasVerif/aeneas/issues/500
fn issue500_1(s: &mut bool) {
    fn bar(_a: &mut bool) {}

    let mut a = *s;
    while 0 < 0 {
        bar(&mut a);
    }
    *s = a;
}

/// Comes from: https://github.com/AeneasVerif/aeneas/issues/500
fn issue500_2(s: &mut [bool; 1]) {
    struct A([bool; 1]);
    fn bar(_a: &mut [bool; 1]) {}

    let mut a = A(*s);
    while false {
        bar(&mut a.0);
    }
    *s = a.0;
}

/// Comes from: https://github.com/AeneasVerif/aeneas/issues/500
fn issue500_3(s: &mut [bool; 1]) {
    struct A([bool; 1]);
    let mut a = A(*s);
    while 0 < 0 {}
    *s = a.0;
}

/// Comes from: https://github.com/AeneasVerif/aeneas/issues/351
fn issue351<'a>(h: &'a u8, mut t: &'a List<u8>) -> &'a u8 {
    let mut last = h;
    while let List::Cons(ht, tt) = t {
        last = ht;
        t = &*tt;
    }
    return last;
}

/// https://github.com/AeneasVerif/aeneas/issues/270
fn issue270(v: &List<List<u8>>) -> Option<&List<u8>> {
    fn box_get_borrow<'a, T>(x: &Box<T>) -> &T {
        &*x
    }
    if let List::Cons(h, t) = v {
        let mut t = box_get_borrow(t);
        let mut last = h;
        while let List::Cons(ht, tt) = t {
            last = ht;
            t = box_get_borrow(tt);
        }
        Some(last)
    } else {
        None
    }
}

/// https://github.com/AeneasVerif/aeneas/issues/400
fn issue400_1(a: &mut i32, b: &mut i32, cond: bool) {
    let mut y = &mut *a;
    let mut i = 0;
    while i < 32 {
        if cond {
            y = &mut *a;
        } else {
            y = &mut *b;
        }
        i += 1;
    }
}

/// https://github.com/AeneasVerif/aeneas/issues/400
fn issue400_2(a: &mut i32, b: &mut i32, c: &mut i32, conds: &[bool]) {
    let mut y = &mut *a;
    let mut z = &mut *b;
    let mut i = 0;
    while i < conds.len() {
        if conds[i] {
            y = &mut *a;
            z = &mut *b;
        } else {
            y = &mut *b;
            z = &mut *c;
        }
        i += 1;
    }
    *y += 3;
    *z += 5;
}

/// Access a global in a loop
fn copy_carray(a: &mut [u32; 2]) {
    const CARRAY: [u32; 2] = [0, 1];
    let mut i = 0;
    while i < 2 {
        a[i] = CARRAY[i];
        i += 1;
    }
}

/// This test used to be only borrow-checked
fn iter_local_mut_borrow() {
    let mut x = 0;
    let mut p = &mut x;
    loop {
        p = &mut (*p);
        *p += 1;

        if *p == 10 {
            break;
        }
    }
}

/// This test used to be only borrow-checked
fn iter_local_shared_borrow() {
    let mut x = 0;
    let mut p = &x;
    loop {
        p = &(*p);

        if x == 0 {
            break;
        }
    }
}

pub enum AList<T> {
    Cons(usize, T, Box<AList<T>>),
    Nil,
}

// This is adapted from the hashmap
fn insert_in_list<T>(key: usize, value: T, mut ls: &mut AList<T>) -> bool {
    loop {
        match ls {
            AList::Nil => {
                *ls = AList::Cons(key, value, Box::new(AList::Nil));
                return true;
            }
            AList::Cons(ckey, cvalue, tl) => {
                if *ckey == key {
                    *cvalue = value;
                    return false;
                } else {
                    ls = tl;
                }
            }
        }
    }
}

// Issue: https://github.com/AeneasVerif/aeneas/issues/641
// The code is adapted from https://github.com/dalek-cryptography/curve25519-dalek
fn reborrow_const() {
    fn reborrow(x: &u64) -> u64 {
        {
            *x
        }
    }
    let i = 0;
    while i < 5 {
        let x = reborrow(&0);
    }
}
