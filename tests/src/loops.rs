use std::vec::Vec;

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

/// Same as [list_nth_mut] but with a loop
pub fn list_nth_mut_loop<T>(mut ls: &mut List<T>, mut i: u32) -> &mut T {
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

/// Same as [list_nth_mut_loop] but with shared borrows
pub fn list_nth_shared_loop<T>(mut ls: &List<T>, mut i: u32) -> &T {
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

/// Small variation of [list_nth_mut_loop]
pub fn list_nth_mut_loop_with_id<T>(ls: &mut List<T>, mut i: u32) -> &mut T {
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

/// Small variation of [list_nth_shared_loop]
pub fn list_nth_shared_loop_with_id<T>(ls: &List<T>, mut i: u32) -> &T {
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
pub fn list_nth_mut_loop_pair<'a, 'b, T>(
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

/// Same as [list_nth_mut_loop_pair] but with shared borrows.
pub fn list_nth_shared_loop_pair<'a, 'b, T>(
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

/// Same as [list_nth_mut_loop_pair] but this time we force the two loop
/// regions to be merged.
pub fn list_nth_mut_loop_pair_merge<'a, T>(
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

/// Same as [list_nth_mut_loop_pair_merge] but with shared borrows.
pub fn list_nth_shared_loop_pair_merge<'a, T>(
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
pub fn list_nth_mut_shared_loop_pair<'a, 'b, T>(
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

/// Same as [list_nth_mut_shared_loop_pair] but this time we force the two loop
/// regions to be merged.
pub fn list_nth_mut_shared_loop_pair_merge<'a, T>(
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

/// Same as [list_nth_mut_shared_loop_pair], but we switched the positions of
/// the mutable and shared borrows.
pub fn list_nth_shared_mut_loop_pair<'a, 'b, T>(
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

/// Same as [list_nth_mut_shared_loop_pair_merge], but we switch the positions of
/// the mutable and shared borrows.
pub fn list_nth_shared_mut_loop_pair_merge<'a, T>(
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
#[allow(clippy::empty_loop)]
pub fn ignore_input_mut_borrow(_a: &mut u32, mut i: u32) {
    while i > 0 {
        i -= 1;
    }
}

// We do not use the input borrow inside the loop
#[allow(clippy::empty_loop)]
pub fn incr_ignore_input_mut_borrow(a: &mut u32, mut i: u32) {
    *a += 1;
    while i > 0 {
        i -= 1;
    }
}

// We do not use the input borrow inside the loop
#[allow(clippy::empty_loop)]
pub fn ignore_input_shared_borrow(_a: &mut u32, mut i: u32) {
    while i > 0 {
        i -= 1;
    }
}
