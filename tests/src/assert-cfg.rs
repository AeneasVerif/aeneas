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
