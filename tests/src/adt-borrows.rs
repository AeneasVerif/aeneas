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

struct MutWrapper<'a, T>(&'a mut T);

impl<'a, T> MutWrapper<'a, T> {
    fn create(x: &'a mut T) -> Self {
        MutWrapper(x)
    }

    fn unwrap(self: Self) -> &'a mut T {
        self.0
    }
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
