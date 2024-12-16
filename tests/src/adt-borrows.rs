//@ [coq,fstar] subdir=misc
//! This file contains tests with ADTs containing borrows.

//
// Structures with borrows
//
struct SharedWrapper<'a, T>(&'a T);

impl<'a, T> SharedWrapper<'a, T> {
    fn create(x: &'a T) -> Self {
        SharedWrapper(x)
    }

    fn unwrap(self: Self) -> &'a T {
        self.0
    }
}

fn use_shared_wrapper() {
    let x: i32 = 0;
    let w = SharedWrapper::create(&x);
    let p = w.unwrap();
    assert!(x == *p);
}

struct SharedWrapper1<'a, T> {
    x: &'a T,
}

impl<'a, T> SharedWrapper1<'a, T> {
    fn create(x: &'a T) -> Self {
        SharedWrapper1 { x }
    }

    fn unwrap(self: Self) -> &'a T {
        self.x
    }
}

fn use_shared_wrapper1() {
    let x: i32 = 0;
    let w = SharedWrapper1::create(&x);
    let p = w.unwrap();
    assert!(x == *p);
}

struct SharedWrapper2<'a, 'b, T> {
    x: &'a T,
    y: &'b T,
}

impl<'a, 'b, T> SharedWrapper2<'a, 'b, T> {
    fn create(x: &'a T, y: &'b T) -> Self {
        SharedWrapper2 { x, y }
    }

    fn unwrap(self: Self) -> (&'a T, &'b T) {
        (self.x, self.y)
    }
}

fn use_shared_wrapper2() {
    let x: i32 = 0;
    let y: i32 = 1;
    let w = SharedWrapper2::create(&x, &y);
    let (px, py) = w.unwrap();
    assert!(x == *px);
    assert!(y == *py);
}

struct MutWrapper<'a, T>(&'a mut T);

impl<'a, T> MutWrapper<'a, T> {
    fn create(x: &'a mut T) -> Self {
        MutWrapper(x)
    }

    fn unwrap(self: Self) -> &'a mut T {
        self.0
    }
}

fn use_mut_wrapper() {
    let mut x: i32 = 0;
    let w = MutWrapper::create(&mut x);
    let p = w.unwrap();
    *p += 1;
    assert!(x == 1);
}

struct MutWrapper1<'a, T> {
    x: &'a mut T,
}

impl<'a, T> MutWrapper1<'a, T> {
    fn create(x: &'a mut T) -> Self {
        MutWrapper1 { x }
    }

    fn unwrap(self: Self) -> &'a mut T {
        self.x
    }
}

fn use_mut_wrapper1() {
    let mut x: i32 = 0;
    let w = MutWrapper1::create(&mut x);
    let p = w.unwrap();
    *p += 1;
    assert!(x == 1);
}

struct MutWrapper2<'a, 'b, T> {
    x: &'a mut T,
    y: &'b mut T,
}

impl<'a, 'b, T> MutWrapper2<'a, 'b, T> {
    fn create(x: &'a mut T, y: &'b mut T) -> Self {
        MutWrapper2 { x, y }
    }

    fn unwrap(self: Self) -> (&'a mut T, &'b mut T) {
        (self.x, self.y)
    }
}

fn use_mut_wrapper2() {
    let mut x: i32 = 0;
    let mut y: i32 = 10;
    let w = MutWrapper2::create(&mut x, &mut y);
    let (px, py) = w.unwrap();
    *px += 1;
    *py += 1;
    assert!(x == 1);
    assert!(y == 11);
}

//
// Arrays/slices containing borrows
//
// Those have the peculiarity of requiring the manipulation of non-expandable
// symbolic values containing borrows.
//

fn array_shared_borrow<'a, const N: usize>(x: [&'a u32; N]) -> [&'a u32; N] {
    x
}

fn array_mut_borrow<'a, const N: usize>(x: [&'a mut u32; N]) -> [&'a mut u32; N] {
    x
}

fn boxed_slice_shared_borrow(x : Box<[&u32]>) -> Box<[&u32]> {
    x
}

fn boxed_slice_mut_borrow(x : Box<[&mut u32]>) -> Box<[&mut u32]> {
    x
}
