//@ [!lean] skip
//! Tests for `#[verify::keep_alive]` on raw-pointer constructors, joins,
//! loops, shared borrows, duplicate calls, and caller return lifetimes.
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::opaque]
pub struct Ptr<T> {
    data: *mut T,
}

impl<T> Copy for Ptr<T> {}
impl<T> Clone for Ptr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Ptr<T> {
    #[verify::opaque]
    pub fn as_shr<'a>(self) -> &'a T {
        unsafe { &*(self.data) }
    }

    #[verify::opaque]
    pub fn as_mut<'a>(self) -> &'a mut T {
        unsafe { &mut *(self.data) }
    }

    #[verify::keep_alive]
    #[verify::opaque]
    pub fn from_mut<'a>(r: &'a mut T) -> Ptr<T> {
        Self { data: &raw mut *r }
    }

    #[verify::keep_alive]
    #[verify::opaque]
    pub fn from_shr<'a>(r: &'a T) -> Self {
        Self {
            data: (&raw const *r) as *mut _,
        }
    }

    #[verify::keep_alive(regular)]
    #[verify::opaque]
    pub fn from_mut_regular<'a>(r: &'a mut T) -> Ptr<T> {
        Self { data: &raw mut *r }
    }

    #[verify::keep_alive(regular)]
    #[verify::opaque]
    pub fn from_shr_regular<'a>(r: &'a T) -> Self {
        Self {
            data: (&raw const *r) as *mut _,
        }
    }

    #[verify::keep_alive(short)]
    #[verify::opaque]
    pub fn from_mut_short<'a>(r: &'a mut T) -> Ptr<T> {
        Self { data: &raw mut *r }
    }
}

pub fn id_mut<'a, T>(x: &'a mut T) -> &'a mut T {
    x
}

pub fn freeze<'a, T>(x: &'a mut T) -> &'a T {
    x
}

pub fn example() {
    let mut x = 42;
    let ptr = Ptr::from_mut(&mut x);
    let xref = ptr.as_mut();
    *xref += 1;
    assert_eq!(x, 43);
}

pub fn example_join_real_input(cond: bool) {
    let mut x = 42;
    let mut y = 0;
    let r = if cond {
        let _ptr = Ptr::from_mut(&mut x);
        id_mut(&mut y)
    } else {
        id_mut(&mut x)
    };
    *r += 1;
    assert_eq!(x + y, 43);
}

pub fn example_join_no_input_no_hint(cond: bool) {
    let mut x = 42;
    let y = 0;
    let s = if cond {
        let _ptr = Ptr::from_mut(&mut x);
        &y
    } else {
        freeze(&mut x)
    };
    let _ = *s;
    assert_eq!(x, 42);
}

// Calling `Ptr::from_mut` inside a loop produces a unit-input backward
// continuation `fun (_ : Unit) => ...` at the `break`.
pub fn simple_loop_ptr_from_mut(mut n: i32) -> i32 {
    let mut x = 42;
    loop {
        let _ptr = Ptr::from_mut(&mut x);
        if n <= 0 {
            break;
        }
        x += 1;
        n -= 1;
    }
    x
}

#[verify::keep_alive]
pub fn make_ptr_and_mut<'a>(x: &'a mut i32, y: &'a mut i32) -> (Ptr<i32>, &'a mut i32) {
    (Ptr::from_mut(x), y)
}

// `make_ptr_and_mut` returns both `Ptr` and `&mut`; ending `r` before `break`
// leaves `AEndedMutLoan` in the abstraction kept alive by `_ptr`.
pub fn loop_explicit_move_mut(mut n: i32) -> i32 {
    let mut x = 42;
    let mut y = 10;
    loop {
        let rx = &mut x;
        let ry = &mut y;
        let _ptr = {
            let (ptr, r) = make_ptr_and_mut(rx, ry);
            *r += 1;
            ptr
        };
        if n <= 0 {
            break;
        }
        x += 1;
        y += 1;
        n -= 1;
    }
    x + y
}

// Verifies `equiv_ctxs` / `match_abstractions` distinguishes `alive_hint`.
pub fn loop_equiv_alive_hint(mut n: i32, cond: bool, cond2: bool) -> i32 {
    let mut z = 0;
    let y = 0;
    let ry = &y;
    let mut s = if cond { ry } else { freeze(&mut z) };
    loop {
        if n <= 0 {
            break;
        }
        n -= 1;
        if cond2 {
            s = if cond {
                let _ptr = Ptr::from_mut(&mut z);
                ry
            } else {
                freeze(&mut z)
            };
            continue;
        }
        s = ry;
    }
    *s + z
}

pub fn join_mut_loan_vs_shared_loan(cond: bool) -> i32 {
    let mut x = 42;
    let y = 10;
    let r = if cond {
        let _ptr = Ptr::from_mut(&mut x);
        &y
    } else {
        &x
    };
    *r + x
}

fn drop_val<T>(_x: T) {}

pub fn join_mut_loan_vs_bottom(cond: bool, mut b: Box<i32>) -> i32 {
    if cond {
        let _ptr = Ptr::from_mut(&mut b);
    } else {
        drop_val(b);
    }
    0
}

pub fn if_join_keep_alive(cond: bool) -> i32 {
    let mut x = 42;
    let mut y = 10;
    let ptr = if cond {
        Ptr::from_mut(&mut x)
    } else {
        Ptr::from_mut(&mut y)
    };
    let rx = ptr.as_mut();
    *rx += 1;
    x + y
}

pub fn loop_join_keep_alive(mut n: i32) -> i32 {
    let mut x = 42;
    let mut ptr = Ptr::from_mut(&mut x);
    loop {
        if n <= 0 {
            break;
        }
        ptr = Ptr::from_mut(&mut x);
        n -= 1;
    }
    let r = ptr.as_mut();
    *r += 1;
    x
}

pub fn loop_join_end_on_demand(mut n: i32, cond: bool) -> i32 {
    let mut x = 42;
    loop {
        if n <= 0 {
            break;
        }
        n -= 1;
        if cond {
            let _ptr = Ptr::from_mut(&mut x);
        }
    }
    x
}

// Shared-borrow `#[verify::keep_alive]` inside a loop: must converge on Pass 1
// so `from_shr_back ()` runs after `ptr.as_shr()`.
pub fn loop_shr<'a>(mut n: i32, x: &'a u32) -> u32 {
    let mut ptr = Ptr::from_shr(x);
    loop {
        if n <= 0 {
            break;
        }
        ptr = Ptr::from_shr(x);
        n -= 1;
    }
    *ptr.as_shr()
}

fn read_via_shr_ptr(x: &i32) -> i32 {
    let ptr = Ptr::from_shr(x);
    *ptr.as_shr()
}

pub fn duplicate_calls_not_deduped(x: &i32) -> i32 {
    let a = read_via_shr_ptr(x);
    let b = read_via_shr_ptr(x);
    a + b
}

#[verify::keep_alive]
fn keep_mut_and_shared<'c>(_m: &'c mut i32, _s: &'c u32) {}

// Local `a = 20;` must end only `a`'s keep-alive abstraction while caller
// borrow `b: &'a mut i32` stays active and flows into `'a`'s backward function.
#[verify::keep_alive]
pub fn return_keep_alive_with_shared<'a>(
    mut a: i32,
    b: &'a mut i32,
    b_out: &'a mut i32,
    s: &'a u32,
    mut n: i32,
    cond: bool,
) -> &'a mut i32 {
    loop {
        if n <= 0 {
            let bm = b;
            keep_mut_and_shared(&mut a, s);
            keep_mut_and_shared(bm, s);
            break;
        }
        if cond {
            *b = 2;
            break;
        }
        n -= 1;
    }
    a = 20;
    let _ = a;
    b_out
}

#[verify::keep_alive]
fn keep_two_shr<'c>(_r1: &'c i32, _r2: &'c u32) {}

// Distinct non-`'static` shared-borrow sets `{&a, s}` and `{b_shr, s}` must not
// merge, so `b_shr`'s keep-alive borrow flows into `'a`'s backward function.
#[verify::keep_alive]
pub fn return_keep_alive_two_shared<'a>(
    mut a: i32,
    b_shr: &'a i32,
    s: &'a u32,
    mut n: i32,
    cond: bool,
) -> &'a i32 {
    loop {
        if n <= 0 {
            keep_two_shr(&a, s);
            keep_two_shr(b_shr, s);
            break;
        }
        if cond {
            break;
        }
        n -= 1;
    }
    a = 20;
    let _ = a;
    b_shr
}

// `Regular`: kept alive past when the called function returns (stateful back fn).
pub fn regular_straight_line() -> i32 {
    let mut x = 42;
    let ptr = Ptr::from_mut_regular(&mut x);
    let r = ptr.as_mut();
    *r += 1;
    x
}

// `Regular`: joins end the abstractions early inside each branch.
pub fn regular_if_join_ends_early(cond: bool) -> i32 {
    let mut x = 42;
    let mut y = 10;
    let tag = if cond {
        let _ptr = Ptr::from_mut_regular(&mut x);
        1
    } else {
        let _ptr = Ptr::from_mut_regular(&mut y);
        2
    };
    tag + x + y
}

// `Regular`: loops end the abstractions early instead of carrying them across iterations.
pub fn regular_loop_ends_early(mut n: i32) -> i32 {
    let mut x = 42;
    loop {
        if n <= 0 {
            break;
        }
        let _ptr = Ptr::from_mut_regular(&mut x);
        n -= 1;
    }
    x
}

// `Regular` wrapper: inner `Regular` borrow flows into the wrapper's backward fn.
#[verify::keep_alive(regular)]
pub fn regular_wrapper_shr<'a>(x: &'a u32) -> Ptr<u32> {
    Ptr::from_shr_regular(x)
}

pub fn use_regular_wrapper_shr(x: &u32) -> u32 {
    let ptr = regular_wrapper_shr(x);
    *ptr.as_shr()
}

// `Short`: behaves like `Regular` (stateful back fn, ended early at joins).
pub fn short_straight_line_and_join(cond: bool) -> i32 {
    let mut x = 40;
    let ptr = Ptr::from_mut_short(&mut x);
    let r = ptr.as_mut();
    *r += 2;
    let bonus = if cond {
        let _p = Ptr::from_mut_short(&mut x);
        0
    } else {
        0
    };
    x + bonus
}

#[cfg(test)]
mod test {
    #[test]
    fn test_raw_example() {
        super::example();
    }
    #[test]
    fn test_example_join_real_input() {
        super::example_join_real_input(true);
        super::example_join_real_input(false);
    }
    #[test]
    fn test_example_join_no_input_no_hint() {
        super::example_join_no_input_no_hint(true);
        super::example_join_no_input_no_hint(false);
    }
    #[test]
    fn test_simple_loop_ptr_from_mut() {
        assert_eq!(super::simple_loop_ptr_from_mut(25), 67);
    }
    #[test]
    fn test_loop_explicit_move_mut() {
        assert_eq!(super::loop_explicit_move_mut(5), 68);
    }
    #[test]
    fn test_loop_equiv_alive_hint() {
        assert_eq!(super::loop_equiv_alive_hint(2, false, false), 0);
    }
    #[test]
    fn test_join_mut_loan_vs_shared_loan() {
        assert_eq!(super::join_mut_loan_vs_shared_loan(true), 52);
        assert_eq!(super::join_mut_loan_vs_shared_loan(false), 84);
    }
    #[test]
    fn test_join_mut_loan_vs_bottom() {
        assert_eq!(super::join_mut_loan_vs_bottom(true, Box::new(42)), 0);
        assert_eq!(super::join_mut_loan_vs_bottom(false, Box::new(42)), 0);
    }
    #[test]
    fn test_if_join_keep_alive() {
        assert_eq!(super::if_join_keep_alive(true), 53);
        assert_eq!(super::if_join_keep_alive(false), 53);
    }
    #[test]
    fn test_loop_join_keep_alive() {
        assert_eq!(super::loop_join_keep_alive(5), 43);
    }
    #[test]
    fn test_loop_join_end_on_demand() {
        assert_eq!(super::loop_join_end_on_demand(0, true), 42);
        assert_eq!(super::loop_join_end_on_demand(2, true), 42);
        assert_eq!(super::loop_join_end_on_demand(2, false), 42);
    }
    #[test]
    fn test_loop_shr() {
        let x = 99u32;
        assert_eq!(super::loop_shr(4, &x), 99);
    }
    #[test]
    fn test_duplicate_calls_not_deduped() {
        let x = 21;
        assert_eq!(super::duplicate_calls_not_deduped(&x), 42);
    }
    #[test]
    fn test_return_keep_alive() {
        let mut b = 10;
        let mut b_out = 7;
        let s = 5u32;
        let r = super::return_keep_alive_with_shared(1, &mut b, &mut b_out, &s, 2, false);
        assert_eq!(*r, 7);
        let b_shr = 12;
        let r2 = super::return_keep_alive_two_shared(1, &b_shr, &s, 2, false);
        assert_eq!(*r2, 12);
    }
    #[test]
    fn test_regular_and_short() {
        assert_eq!(super::regular_straight_line(), 43);
        assert_eq!(super::regular_if_join_ends_early(true), 53);
        assert_eq!(super::regular_if_join_ends_early(false), 54);
        assert_eq!(super::regular_loop_ends_early(3), 42);
        let u = 77u32;
        assert_eq!(super::use_regular_wrapper_shr(&u), 77);
        assert_eq!(super::short_straight_line_and_join(true), 42);
        assert_eq!(super::short_straight_line_and_join(false), 42);
    }
}
