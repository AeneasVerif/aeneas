//@ [!lean] skip

fn get_b0() -> bool {
    true
}

fn get_b1() -> bool {
    true
}

fn f() {}

// === Patterns with boolean inputs ===

pub fn assert_or(b0: bool, b1: bool) {
    assert!(b0 || b1);
    f();
}

pub fn assert_and(b0: bool, b1: bool) {
    assert!(b0 && b1);
    f();
}

pub fn assert_not_or(b0: bool, b1: bool) {
    assert!(!(b0 || b1));
    f();
}

pub fn assert_not_and(b0: bool, b1: bool) {
    assert!(!(b0 && b1));
    f();
}

pub fn assert_not_b0_or_b1(b0: bool, b1: bool) {
    assert!(!b0 || b1);
    f();
}

pub fn assert_b0_or_not_b1(b0: bool, b1: bool) {
    assert!(b0 || !b1);
    f();
}

pub fn assert_not_b0_or_not_b1(b0: bool, b1: bool) {
    assert!(!b0 || !b1);
    f();
}

pub fn assert_not_b0_and_b1(b0: bool, b1: bool) {
    assert!(!b0 && b1);
    f();
}

pub fn assert_b0_and_not_b1(b0: bool, b1: bool) {
    assert!(b0 && !b1);
    f();
}

pub fn assert_not_b0_and_not_b1(b0: bool, b1: bool) {
    assert!(!b0 && !b1);
    f();
}

// === Patterns with function calls ===

pub fn assert_or_call() {
    assert!(get_b0() || get_b1());
    f();
}

pub fn assert_and_call() {
    assert!(get_b0() && get_b1());
    f();
}

pub fn assert_not_or_call() {
    assert!(!(get_b0() || get_b1()));
    f();
}

pub fn assert_not_and_call() {
    assert!(!(get_b0() && get_b1()));
    f();
}

pub fn assert_not_b0_or_b1_call() {
    assert!(!get_b0() || get_b1());
    f();
}

pub fn assert_b0_or_not_b1_call() {
    assert!(get_b0() || !get_b1());
    f();
}

pub fn assert_not_b0_or_not_b1_call() {
    assert!(!get_b0() || !get_b1());
    f();
}

pub fn assert_not_b0_and_b1_call() {
    assert!(!get_b0() && get_b1());
    f();
}

pub fn assert_b0_and_not_b1_call() {
    assert!(get_b0() && !get_b1());
    f();
}

pub fn assert_not_b0_and_not_b1_call() {
    assert!(!get_b0() && !get_b1());
    f();
}

// === Patterns with comparison-based asserts ===

pub fn assert_lt(x: u32) {
    assert!(x < 10);
    f();
}

pub fn assert_le(x: u32) {
    assert!(x <= 3494);
    f();
}

pub fn assert_gt(x: u32) {
    assert!(x > 0);
    f();
}

pub fn assert_ge(x: u32) {
    assert!(x >= 1);
    f();
}

pub fn assert_eq(x: u32) {
    assert!(x == 42);
    f();
}

pub fn assert_ne(x: u32) {
    assert!(x != 0);
    f();
}

pub fn assert_arith(x: u32, y: u32) {
    assert!(x + y < 100);
    f();
}

// === Patterns with asserts inside loop bodies ===
// Minimized from SymCrypt's poly_element_mul_and_accumulate and
// montgomery_reduce_and_add_poly_element_accumulator_to_poly_element.

/// Assert in a loop body.
/// Before the fix, asserts in loop bodies were not reconstructed as `massert`
/// because `intro_massert` ran before loop decomposition.
fn assert_in_loop(a: &[u32; 10]) {
    for i in 0usize..10 {
        let x = a[i];
        assert!(x < 100);
    }
}

/// Assert with OR condition in a loop body.
/// The pattern `assert!((c >= X) || (c < Y))` in a loop body triggered
/// a missing `do` in the generated Lean: the OR reconstruction created a nested
/// monadic Let inside the rhs of another Let, but the extraction didn't emit `do`.
fn assert_or_in_loop(a: &mut [u32; 10]) {
    for i in 0usize..10 {
        let mut c: u32 = a[i];
        assert!(c < 100);
        // wrapping_sub followed by OR assert: the typical constant-time
        // range reduction pattern from crypto code
        c = c.wrapping_sub(200);
        assert!((c >= ((-200i32) as u32)) || (c < 100));
        c = c.wrapping_add(100 & (c >> 16));
        assert!((c >= ((-100i32) as u32)) || (c < 100));
        c = c.wrapping_add(100 & (c >> 16));
        assert!(c < 100);
        a[i] = c;
    }
}
