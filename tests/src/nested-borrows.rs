//@ [!lean] skip
//! This module contains functions with nested borrows in their signatures.
#![feature(register_tool)]
#![register_tool(aeneas)]

trait Trait1 {
    fn f(x: &&u32);
}

fn inner_shared<'a, 'b>(x : &'a &'b u32) -> &'b u32 {
    *x
}

fn inner_mut<'a, 'b>(x : &'a mut &'b mut u32) -> &'a mut u32 {
    *x
}

fn call_inner_mut() {
    let mut x = 0;
    let mut px = &mut x;
    let py = inner_mut(&mut px);
    *py = 1;
    assert!(*px == 1);
    *px = 2;
    assert!(x == 2);
}

fn inner_mut_swap<'a, 'b>(ppx : &'a mut &'b mut u32, py : &'b mut u32) -> &'a mut u32 {
    **ppx = 10;
    *ppx = py;
    *ppx
}

fn call_inner_mut_swap() {
    let mut x = 0;
    let mut px = &mut x;
    let mut y = 1;
    let mut py = &mut y;
    let pz = inner_mut_swap(&mut px, py);
    *pz = 2;
    assert!(*px == 2); // px now points to y
    *px = 3;
    assert!(x == 10);
    assert!(y == 3);
}

fn incr_inner<'a, 'b>(x : &'a mut &'b mut u32) {
    **x += 1;
}

struct IterMut<'a, T> {
    v : Option<&'a mut T>,
}

// TODO: fix in Charon
fn replace_option_mut<'a, 'b, T>(x : &'a mut Option<&'b mut T>, v : Option<&'b mut T>) -> Option<&'b mut T> {
    panic!() // std::mem::replace(x, v)
}

impl<'a, T> IterMut<'a, T> {
    fn next(&mut self) -> Option<&'a mut T> {
        /* We need to use `std::mem::replace` because otherwise the
           code doesn't borrow-check. */
        replace_option_mut(&mut self.v, None)
    }
}

fn call_iter_mut_next<'a, T>(mut it : IterMut<'a, T>) {
    match it.next() {
        None => (),
        Some (_) => (),
    }
}

fn call_iter_mut_next_u32<'a, T>(mut it : IterMut<'a, u32>) {
    match it.next() {
        None => (),
        Some (x) => *x += 1,
    }
}

fn iter_mut_loop<'a, T>(mut it : IterMut<'a, T>) {
    while let Some(_) = it.next() {}
}

fn iter_mut_incr<'a, T>(mut it : IterMut<'a, u32>) {
    while let Some(x) = it.next() {
        *x += 1;
    }
}

enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

struct ListIterMut<'a, T> {
    current: Option<&'a mut List<T>>,
}

impl<T> List<T> {
    pub fn iter_mut<'a>(&'a mut self) -> ListIterMut<'a, T> {
        ListIterMut {
            current: Some(self),
        }
    }
}

// TODO: fix in Charon
fn take_option_mut<'a, 'b, T>(x : &'a mut Option<&'b mut T>) -> Option<&'b mut T> {
    panic!() // x.take()
}

impl<'a, T> ListIterMut<'a, T> {
    fn next(&mut self) -> Option<&'a mut T> {
        // TODO: self.current.take()
        match take_option_mut(&mut self.current) {
            Some(&mut List::Cons(ref mut value, ref mut next)) => {
                self.current = Some(next);
                Some(value)
            }
            _ => None,
        }
    }
}

fn incr_list(l : &mut List<u32>) {
    let mut it = l.iter_mut();
    while let Some(x) = it.next() {
        *x += 1;
    }
}

/*
pub fn id_mut_mut<'a, 'b, T>(x: &'a mut &'b mut T) -> &'a mut &'b mut T {
    x
}

pub fn id_mut_pair<'a, T>(x: &'a mut (&'a mut T, u32)) -> &'a mut (&'a mut T, u32) {
    x
}

pub fn id_mut_pair_test1() {
    let mut x: u32 = 0;
    let px = &mut x;
    let mut p = (px, 1);
    let pp0 = &mut p;
    let pp1 = id_mut_pair(pp0);
    let mut y = 2;
    *pp1 = (&mut y, 3);
}

pub fn id_mut_mut_pair<'a, T>(
    x: &'a mut &'a mut (&'a mut T, u32),
) -> &'a mut &'a mut (&'a mut T, u32) {
    x
}

pub fn id_mut_mut_mut_same<'a, T>(x: &'a mut &'a mut &'a mut u32) -> &'a mut &'a mut &'a mut u32 {
    x
}

pub fn id_borrow1<'a, 'b, 'c>(_x: &'a mut &'b u32, _y: &'a &'a mut u32) {
    ()
}

/// For symbolic execution: testing what happens with several abstractions.
pub fn id_mut_mut_test1() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    let ppy = id_mut_mut(ppx);
    **ppy = 1;
    // Ending one abstraction
    assert!(*px == 1);
    // Ending the other abstraction
    assert!(x == 1);
}*/

/*
/// For symbolic execution: testing what happens with several abstractions.
/// This case is a bit trickier, because we modify the borrow graph through
/// a value returned by a function call.
/// TODO: not supported! We overwrite a borrow in a returned value.
pub fn id_mut_mut_test2() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    let ppy = id_mut_mut(ppx);
    **ppy = 1;
    // This time, we replace one of the borrows
    let mut y = 2;
    let py = &mut y;
    *ppy = py;
    // Ending one abstraction
    assert!(*px == 2);
    *px = 3;
    // Ending the other abstraction
    assert!(x == 1);
    assert!(y == 3);
}
*/

/*
/// For symbolic execution: testing what happens with several abstractions.
/// See what happens when chaining function calls.
/// TODO: not supported! We overwrite a borrow in a returned value.
pub fn id_mut_mut_test3() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    let ppy = id_mut_mut(ppx); // &'a mut &'b mut i32
    **ppy = 1;
    let ppz = id_mut_mut(ppy); // &'c mut &'b mut i32
    **ppz = 2;
    // End 'a and 'c
    assert!(*px == 2);
    // End 'b (2 abstractions at once)
    assert!(x == 2);
}*/

/*
/// For symbolic execution: testing what happens with several abstractions.
/// See what happens when chaining function calls.
/// This one is slightly more complex than the previous one.
pub fn id_mut_mut_test4() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    let ppy = id_mut_mut(ppx); // &'a mut &'b mut i32
    **ppy = 1;
    let ppz = id_mut_mut(ppy); // &'c mut &'b mut i32
    **ppz = 2;
    // End 'c
    assert!(**ppy == 2);
    // End 'a
    assert!(*px == 2);
    // End 'b (2 abstractions at once)
    assert!(x == 2);
}
*/

/*
fn id<'a, T>(x: &'a mut T) -> &'a mut T {
    x
}

/// Checking projectors over symbolic values
pub fn test_borrows1() {
    let mut x = 3;
    let y = id(&mut x);
    let z = id(y);
    // We do not write a statement which would expand `z` on purpose:
    // we want to test that the handling of non-expanded symbolic values
    // is correct
    assert!(x == 3);
}

fn id_pair<'a, 'b, T>(x: &'a mut T, y: &'b mut T) -> (&'a mut T, &'b mut T) {
    (x, y)
}

/// Similar to the previous one
pub fn test_borrows2() {
    let mut x = 3;
    let mut y = 4;
    let z = id_pair(&mut x, &mut y);
    // We do not write a statement which would expand `z` on purpose:
    // we want to test that the handling of non-expanded symbolic values
    // is correct
    assert!(x == 3);
    assert!(y == 4);
}

/// input type: 'b must last longer than 'a
/// output type: 'a must last longer than 'b
/// So: 'a = 'b, and the function is legal.
pub fn nested_mut_borrows1<'a, 'b>(x: &'a mut &'b mut u32) -> &'b mut &'a mut u32 {
    x
}

pub fn nested_shared_borrows1<'a, 'b>(x: &'a &'b u32) -> &'a &'b u32 {
    x
}

pub fn nested_borrows1<'a, 'b>(x: &'a mut &'b u32) -> &'a mut &'b u32 {
    x
}

pub fn nested_borrows2<'a, 'b>(x: &'a &'b mut u32) -> &'a &'b mut u32 {
    x
}

fn nested_borrows1_test1() {
    let x = 0;
    let mut px = &x;
    let ppx = &mut px;
    let ppy = nested_borrows1(ppx);
    assert!(**ppy == 0);
    assert!(x == 0);
}

fn nested_borrows1_test2<'a, 'b>(x: &'a mut &'b u32) -> &'a mut &'b u32 {
    nested_borrows1(x)
}

fn nested_borrows2_test1() {
    let mut x = 0;
    let px = &mut x;
    let ppx = &px;
    let ppy = nested_borrows2(ppx);
    assert!(**ppy == 0);
    assert!(x == 0);
}
*/
