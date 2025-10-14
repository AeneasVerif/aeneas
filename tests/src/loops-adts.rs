//@ [!lean] skip

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

pub fn nth_shared<T>(mut ls: &List<T>, mut i: u32) -> Option<&T> {
    while let List::Cons(x, tl) = ls {
        if i == 0 {
            return Some(x);
        } else {
            ls = tl;
            i -= 1;
        }
    }
    None
}

pub fn nth_mut<T>(mut ls: &mut List<T>, mut i: u32) -> Option<&mut T> {
    while let List::Cons(x, tl) = ls {
        if i == 0 {
            return Some(x);
        } else {
            ls = tl;
            i -= 1;
        }
    }
    None
}

pub fn update_array_mut_borrow(a: [&mut u32; 32]) -> [&mut u32; 32] {
    a
}

pub fn array_mut_borrow_loop1(b: bool, mut a: [&mut u32; 32]) {
    while b {
        a = update_array_mut_borrow(a)
    }
}

pub fn array_mut_borrow_loop2(b: bool, mut a: [&mut u32; 32]) -> [&mut u32; 32] {
    while b {
        a = update_array_mut_borrow(a)
    }
    a
}

pub fn copy_shared_array(a: [&u32; 32]) -> [&u32; 32] {
    a
}

pub fn array_shared_borrow_loop1(b: bool, mut a: [&u32; 32]) {
    while b {
        a = copy_shared_array(a)
    }
}

pub fn array_shared_borrow_loop2(b: bool, mut a: [&u32; 32]) -> [&u32; 32] {
    while b {
        a = copy_shared_array(a)
    }
    a
}
