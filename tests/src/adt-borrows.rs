//@ [coq,fstar] subdir=misc
//! This file contains tests with ADTs containing borrows.

struct SharedWrapper<'a, T>(&'a T);

impl<'a, T> SharedWrapper<'a, T> {
    fn create(x: &'a T) -> Self {
        SharedWrapper(x)
    }

    fn unwrap(self: Self) -> &'a T {
        self.0
    }
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
