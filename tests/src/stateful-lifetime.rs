//@ [!lean] skip
//! Tests for `#[verify::stateful_lifetime]` on raw-pointer constructors, joins,
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
    #[verify::stateful_lifetime(short)]
    #[verify::opaque]
    pub fn as_shr<'a>(self) -> &'a T {
        unsafe { &*(self.data) }
    }

    #[verify::stateful_lifetime(short)]
    #[verify::opaque]
    pub fn as_mut<'a>(self) -> &'a mut T {
        unsafe { &mut *(self.data) }
    }

    #[verify::stateful_lifetime(long)]
    #[verify::opaque]
    pub fn from_mut<'a>(r: &'a mut T) -> Ptr<T> {
        Self { data: &raw mut *r }
    }

    #[verify::stateful_lifetime(long)]
    #[verify::opaque]
    pub fn from_shr<'a>(r: &'a T) -> Self {
        Self {
            data: (&raw const *r) as *mut _,
        }
    }

    #[verify::stateful_lifetime(default)]
    #[verify::opaque]
    pub fn from_mut_regular<'a>(r: &'a mut T) -> Ptr<T> {
        Self { data: &raw mut *r }
    }

    #[verify::stateful_lifetime('a)]
    #[verify::opaque]
    pub fn from_shr_regular<'a>(r: &'a T) -> Self {
        Self {
            data: (&raw const *r) as *mut _,
        }
    }

    #[verify::stateful_lifetime('a, short)]
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

pub fn example_two_derefs() {
    let mut x = 42;
    let ptr = Ptr::from_mut(&mut x);
    let r1 = ptr.as_mut();
    *r1 += 1;
    let s = ptr.as_shr();
    let v = *s;
    let r2 = ptr.as_mut();
    *r2 = v + 10;
    assert_eq!(x, 53);
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

#[verify::stateful_lifetime('a, long)]
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

// Verifies `equiv_ctxs` / `match_abstractions` distinguishes `stateful_lifetime`.
pub fn loop_equiv_stateful_lifetime(mut n: i32, cond: bool, cond2: bool) -> i32 {
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

pub fn if_join_stateful_lifetime(cond: bool) -> i32 {
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

pub fn loop_join_stateful_lifetime(mut n: i32) -> i32 {
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

// Shared-borrow `#[verify::stateful_lifetime]` inside a loop: must converge on Pass 1
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

#[verify::stateful_lifetime('c, long)]
fn keep_mut_and_shared<'c>(_m: &'c mut i32, _s: &'c u32) {}

// Local `a = 20;` must end only `a`'s stateful-lifetime abstraction while caller
// borrow `b: &'a mut i32` stays active and flows into `'a`'s backward function.
#[verify::stateful_lifetime]
pub fn return_stateful_lifetime_with_shared<'a>(
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

#[verify::stateful_lifetime('c, long)]
fn keep_two_shr<'c>(_r1: &'c i32, _r2: &'c u32) {}

// Distinct non-`'static` shared-borrow sets `{&a, s}` and `{b_shr, s}` must not
// merge, so `b_shr`'s stateful-lifetime borrow flows into `'a`'s backward function.
#[verify::stateful_lifetime]
pub fn return_stateful_lifetime_two_shared<'a>(
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

// `Default` wrapper: inner `Default` borrow flows into the wrapper's backward fn.
#[verify::stateful_lifetime('a)]
pub fn regular_wrapper_shr<'a>(x: &'a u32) -> Ptr<u32> {
    Ptr::from_shr_regular(x)
}

pub fn use_regular_wrapper_shr(x: &u32) -> u32 {
    let ptr = regular_wrapper_shr(x);
    *ptr.as_shr()
}

fn side_effect(v: i32) -> i32 {
    v + 100
}

#[verify::stateful_lifetime]
pub fn reborrow_regular<'a>(x: &'a mut i32) -> &'a mut i32 {
    x
}

#[verify::stateful_lifetime('a, short)]
pub fn reborrow_short<'a>(x: &'a mut i32) -> &'a mut i32 {
    x
}

// Contrast `Regular` vs `Short` after last use of `r`:
// - `Regular` keeps `r`'s abstraction alive across `side_effect(5)` until `x` is accessed.
pub fn regular_waits_past_unrelated_call() -> i32 {
    let mut x = 10;
    let r = reborrow_regular(&mut x);
    *r += 1;
    let z = side_effect(5);
    x + z
}

// - `Short` ends `reborrow_short` immediately after `*r += 1`, BEFORE `side_effect(5)`.
pub fn short_ends_after_last_use() -> i32 {
    let mut x = 10;
    let r = reborrow_short(&mut x);
    *r += 1;
    let z = side_effect(5);
    x + z
}

// Transitive reborrow: `r1` dies right after `id_mut(r1)`, but `r2` stays live across
// `side_effect(1)`, so `reborrow_short` stays alive until after `*r2 += a`, ending
// before `side_effect(2)`.
pub fn short_chained_reborrow() -> i32 {
    let mut x = 10;
    let r1 = reborrow_short(&mut x);
    let r2 = id_mut(r1);
    let a = side_effect(1);
    *r2 += a;
    let b = side_effect(2);
    x + b
}

// `let _ = *r;` (`PlaceMention(*r)`) counts as a live use, keeping `reborrow_short`
// alive across `side_effect(1)` and ending it right before `side_effect(2)`.
pub fn short_place_mention_extends_life() -> i32 {
    let mut x = 10;
    let r = reborrow_short(&mut x);
    *r += 1;
    let a = side_effect(1);
    let _ = *r;
    let b = side_effect(2);
    x + a + b
}

#[verify::opaque]
pub struct Guard<'a> {
    data: &'a mut i32,
}

impl<'a> Guard<'a> {
    #[verify::stateful_lifetime(short)]
    #[verify::opaque]
    pub fn acquire(x: &'a mut i32) -> Guard<'a> {
        Guard { data: x }
    }

    #[verify::opaque]
    pub fn get_mut<'b>(&'b mut self) -> &'b mut i32 {
        self.data
    }

    #[verify::opaque]
    pub fn get_shr<'b>(&'b self) -> &'b i32 {
        self.data
    }

    #[verify::stateful_lifetime('a)]
    #[verify::opaque]
    pub fn refresh_regular(self) -> Guard<'a> {
        self
    }

    #[verify::stateful_lifetime('a, short)]
    #[verify::opaque]
    pub fn refresh_short(self) -> Guard<'a> {
        self
    }
}

pub fn caller_takes_guard_regular<'a>(g: Guard<'a>) -> i32 {
    let mut g2 = g.refresh_regular();
    let r = g2.get_mut();
    *r += 1;
    side_effect(5)
}

pub fn caller_takes_guard_short<'a>(g: Guard<'a>) -> i32 {
    let mut g2 = g.refresh_short();
    let r = g2.get_mut();
    *r += 1;
    side_effect(5)
}

// Lifetime-carrying ADT (`Guard<'a>`): stays alive across `g.get_mut()` and `*r += 5`,
// then releases immediately before `side_effect(1)`.
pub fn short_guard_releases_early() -> i32 {
    let mut x = 10;
    let mut g = Guard::acquire(&mut x);
    let r = g.get_mut();
    *r += 5;
    let y = side_effect(1);
    x + y
}

// Regression (P1-1a): live `g` temporarily holds `VMutLoan` while borrowed by `get_mut`;
// `Guard::acquire` must stay alive for the second `g.get_mut()`, then end before `side_effect(2)`.
pub fn short_guard_two_get_muts() -> i32 {
    let mut x = 10;
    let mut g = Guard::acquire(&mut x);
    let r1 = g.get_mut();
    *r1 += 5;
    let a = side_effect(1);
    let r2 = g.get_mut();
    *r2 += a;
    let b = side_effect(2);
    x + b
}

// Regression (P1-1b): live `r2` temporarily holds `VMutLoan` inside dead `_rr2 = &mut r2`;
// `reborrow_short` must stay alive until `*r2 += a`, then end before `side_effect(2)`.
pub fn short_temp_mut_borrow_of_live_ref() -> i32 {
    let mut x = 10;
    let r1 = reborrow_short(&mut x);
    let mut r2 = &mut *r1;
    let _rr2 = &mut r2;
    let a = side_effect(1);
    *r2 += a;
    let b = side_effect(2);
    x + b
}

#[verify::stateful_lifetime(short)]
pub fn reborrow_pair_shr<'a>(x: &'a (i32, i32)) -> &'a (i32, i32) {
    x
}

// Regression (P1-2): concrete `VSharedLoan` inside `ASharedLoan` created by sub-borrowing
// `&((*p).0)` must keep `reborrow_pair_shr` alive until `*f0` is read.
pub fn short_sub_shared_reborrow() -> i32 {
    let x = (10, 20);
    let p = reborrow_pair_shr(&x);
    let f0 = &((*p).0);
    let z = side_effect(1);
    *f0 + z
}

// Regression (P1-3): nested `VSharedLoan`s inside dead `pair` / `s1` while inner `s2` is live
// must keep `Guard::acquire` alive across `side_effect(1)`, then release before `side_effect(2)`.
pub fn short_nested_shared_proj() -> i32 {
    let mut x = 10;
    let pair = (Guard::acquire(&mut x), 0);
    let s1 = &pair;
    let s2 = &((*s1).0);
    let a = side_effect(1);
    let v = *s2.get_shr();
    let b = side_effect(2);
    v + a + b + x
}

pub struct Holder<'a> {
    pub data: &'a mut i32,
    pub tag: i32,
}

#[verify::stateful_lifetime(short)]
pub fn make_holder<'a>(x: &'a mut i32) -> Holder<'a> {
    Holder { data: x, tag: 0 }
}

// Regression (P1-5): non-deref field write `h.tag = ...` counts as a use of `h` under NLL,
// keeping `make_holder` alive across `side_effect(1)` and ending it before `side_effect(2)`.
#[allow(unused_assignments)]
pub fn short_subplace_field_write() -> i32 {
    let mut x = 10;
    let mut h = make_holder(&mut x);
    *h.data += 5;
    h.tag = side_effect(1);
    let b = side_effect(2);
    x + b
}

// `Short` must not prematurely end an active `Long` abstraction (`Ptr::from_mut`)
// that borrowed from `r`.
pub fn short_does_not_kill_long() -> i32 {
    let mut x = 10;
    let r = reborrow_short(&mut x);
    let ptr = Ptr::from_mut(r);
    let rx = ptr.as_mut();
    *rx += 3;
    x
}

// Zero-loan `Short` call (`Ptr<T>` has no lifetime `'a`): ends immediately before the
// next statement (`side_effect(1)`).
pub fn short_zero_loan_ends_immediately() -> i32 {
    let mut x = 40;
    let _ptr = Ptr::from_mut_short(&mut x);
    let y = side_effect(1);
    x + y
}

// `Short` inside a loop: ends right after `*r += 1` (before `side_effect(1)`) on each iteration.
pub fn short_in_loop(mut n: i32) -> i32 {
    let mut x = 0;
    loop {
        if n <= 0 {
            break;
        }
        let r = reborrow_short(&mut x);
        *r += 1;
        let _ = side_effect(1);
        n -= 1;
    }
    x
}

#[verify::stateful_lifetime('a, short)]
pub fn two_lifetimes_only_a_short<'a, 'b>(
    x: &'a mut i32,
    y: &'b mut i32,
) -> (&'a mut i32, &'b mut i32) {
    (x, y)
}

// `'a` has an effectful `Short` backward function (ends before `side_effect(1)`),
// whereas `'b` has a pure backward function.
pub fn caller_two_lifetimes_only_a_short() -> i32 {
    let mut x = 10;
    let mut y = 20;
    let (rx, ry) = two_lifetimes_only_a_short(&mut x, &mut y);
    *rx += 1;
    let s = side_effect(1);
    *ry += s;
    x + y
}

#[verify::stateful_lifetime('a)]
pub fn two_lifetimes_a_default<'a, 'b>(x: &'a mut i32, y: &'b i32) -> &'a mut i32 {
    *x += *y;
    x
}

// `('a)` defaults to `Default` (stays alive across `side_effect(2)` until `x` is read),
// while `'b` is pure and ends immediately at the call.
pub fn caller_two_lifetimes_a_default() -> i32 {
    let mut x = 10;
    let y = 5;
    let rx = two_lifetimes_a_default(&mut x, &y);
    *rx += 3;
    let z = side_effect(2);
    x + y + z
}

#[verify::stateful_lifetime('a, short)]
#[verify::stateful_lifetime('b, default)]
pub fn two_lifetimes_repeated<'a, 'b>(
    x: &'a mut i32,
    y: &'b mut i32,
) -> (&'a mut i32, &'b mut i32) {
    (reborrow_short(x), reborrow_regular(y))
}

// Repeated per-lifetime attributes: `'a` (`Short`) ends right after `*rx += 1`
// before `side_effect(1)`, while `'b` (`Default`) stays alive across `side_effect(1)`.
pub fn caller_two_lifetimes_repeated() -> i32 {
    let mut x = 10;
    let mut y = 20;
    let (rx, ry) = two_lifetimes_repeated(&mut x, &mut y);
    *rx += 1;
    *ry += 2;
    let s = side_effect(1);
    x + y + s
}

#[verify::stateful_lifetime]
#[verify::stateful_lifetime('a, short)]
pub fn two_lifetimes_wildcard_and_override<'a, 'b>(
    x: &'a mut i32,
    y: &'b mut i32,
) -> (&'a mut i32, &'b mut i32) {
    (x, y)
}

// Bare `#[verify::stateful_lifetime]` gives `'b` `Default`, while `('a, short)`
// overrides `'a` to `Short`.
pub fn caller_two_lifetimes_wildcard_and_override() -> i32 {
    let mut x = 10;
    let mut y = 20;
    let (rx, ry) = two_lifetimes_wildcard_and_override(&mut x, &mut y);
    *rx += 1;
    *ry += 2;
    let s = side_effect(1);
    x + y + s
}

#[verify::stateful_lifetime(short)]
pub fn generic_ty_not_marked_stateful<'a, T>(x: &'a mut i32, extra: T) -> (&'a mut i32, T) {
    (x, extra)
}

// Calling `generic_ty_not_marked_stateful` with `T = &i32` introduces a synthetic
// region group for `T`, which must remain pure (even under wildcard `short`) while
// `'a` is `Short`.
pub fn caller_generic_ty_not_marked_stateful() -> i32 {
    let mut x = 10;
    let y = 20;
    let (rx, ry) = generic_ty_not_marked_stateful(&mut x, &y);
    *rx += 1;
    let s = side_effect(1);
    x + *ry + s
}

#[cfg(test)]
mod test {
    #[test]
    fn test_raw_example() {
        super::example();
        super::example_two_derefs();
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
    fn test_loop_equiv_stateful_lifetime() {
        assert_eq!(super::loop_equiv_stateful_lifetime(2, false, false), 0);
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
    fn test_if_join_stateful_lifetime() {
        assert_eq!(super::if_join_stateful_lifetime(true), 53);
        assert_eq!(super::if_join_stateful_lifetime(false), 53);
    }
    #[test]
    fn test_loop_join_stateful_lifetime() {
        assert_eq!(super::loop_join_stateful_lifetime(5), 43);
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
    fn test_return_stateful_lifetime() {
        let mut b = 10;
        let mut b_out = 7;
        let s = 5u32;
        let r = super::return_stateful_lifetime_with_shared(1, &mut b, &mut b_out, &s, 2, false);
        assert_eq!(*r, 7);
        let b_shr = 12;
        let r2 = super::return_stateful_lifetime_two_shared(1, &b_shr, &s, 2, false);
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
        assert_eq!(super::regular_waits_past_unrelated_call(), 116);
        assert_eq!(super::short_ends_after_last_use(), 116);
        assert_eq!(super::short_chained_reborrow(), 213);
        assert_eq!(super::short_place_mention_extends_life(), 214);
        assert_eq!(super::short_guard_releases_early(), 116);
        let mut gx = 10;
        assert_eq!(
            super::caller_takes_guard_regular(super::Guard::acquire(&mut gx)),
            105
        );
        assert_eq!(gx, 11);
        assert_eq!(
            super::caller_takes_guard_short(super::Guard::acquire(&mut gx)),
            105
        );
        assert_eq!(gx, 12);
        assert_eq!(super::short_guard_two_get_muts(), 218);
        assert_eq!(super::short_temp_mut_borrow_of_live_ref(), 213);
        assert_eq!(super::short_sub_shared_reborrow(), 111);
        assert_eq!(super::short_nested_shared_proj(), 223);
        assert_eq!(super::short_subplace_field_write(), 117);
        assert_eq!(super::short_does_not_kill_long(), 13);
        assert_eq!(super::short_zero_loan_ends_immediately(), 141);
        assert_eq!(super::short_in_loop(4), 4);
        assert_eq!(super::caller_two_lifetimes_only_a_short(), 132);
        assert_eq!(super::caller_two_lifetimes_a_default(), 125);
        assert_eq!(super::caller_two_lifetimes_repeated(), 134);
        assert_eq!(super::caller_two_lifetimes_wildcard_and_override(), 134);
        assert_eq!(super::caller_generic_ty_not_marked_stateful(), 132);
    }
}
