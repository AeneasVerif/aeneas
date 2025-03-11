//@ [!lean] skip

use std::ops::Deref;
use std::ops::DerefMut;

pub fn use_deref_box<T>(x: &Box<T>) -> &T {
    x.deref()
}

pub fn use_deref_mut_box<T>(x: &mut Box<T>) -> &mut T {
    x.deref_mut()
}

pub fn test_deref_box() {
    use std::ops::Deref;
    use std::ops::DerefMut;
    let mut b: Box<i32> = Box::new(0);
    let x = b.deref_mut();
    *x = 1;
    let x = b.deref();
    assert!(*x == 1);
}

pub fn use_deref_vec<T>(x: &Vec<T>) -> &[T] {
    x.deref()
}

pub fn use_deref_mut_vec<T>(x: &mut Vec<T>) -> &mut [T] {
    x.deref_mut()
}
