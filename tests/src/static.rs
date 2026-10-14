//@ [!lean] skip

pub trait WithSlice {
    const SLICE: &'static [u16];
}

/*struct S;
impl WithSlice for S {
    const SLICE : &'static [u16] = &[0, 1];
}

impl S {
    fn read(i : usize) -> u16 {
        S::SLICE[i]
    }

    fn sum() -> u16 {
        let mut s = 0;
        for x in Self::SLICE {
            s += x;
        }
        s
    }
}
*/

fn read<S: WithSlice>(_: S, i: usize) -> u16 {
    S::SLICE[i]
}

/*fn sum<S : WithSlice>(_ : S, i : usize) -> u16 {
    let mut s = 0;
    for x in S::SLICE {
        s += x;
    }
    s
}*/

fn use_static() {
    const PREFIX: &[u8; 1] = &[0];
    let _ = PREFIX;
}

static GLOBAL: u32 = 3;

fn ret_static() -> &'static u32 {
    &GLOBAL
}

fn ret_str() -> &'static str {
    "hello"
}

fn take_static(x: &'static u32) -> u32 {
    *x
}

fn call_take_static() -> u32 {
    take_static(&GLOBAL)
}

fn choose_static<'a>(b: bool, x: &'a u32) -> &'a u32 {
    if b {
        x
    } else {
        &GLOBAL
    }
}

fn branch_str(b: bool) -> &'static str {
    if b {
        "a"
    } else {
        "b"
    }
}

fn loop_global(n: usize) -> u32 {
    const CARRAY: [u32; 2] = [0, 1];
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += CARRAY[i % 2];
        i += 1;
    }
    s
}

fn pair<'a>(x: &'a mut u32) -> (&'a mut u32, &'static u32) {
    (x, &GLOBAL)
}

fn use_pair(y: &mut u32) -> u32 {
    let (a, b) = pair(y);
    *a += 1;
    *b
}

fn incr_static_mut(x: &'static mut u32) {
    *x += 1;
}

fn ret_static_mut(x: &'static mut u32) -> &'static mut u32 {
    x
}

struct StaticRef {
    x: &'static u32,
}

fn mk_static_ref() -> StaticRef {
    StaticRef { x: &GLOBAL }
}

fn loop_take_static(n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += take_static(&GLOBAL);
        i += 1;
    }
    s
}

fn take_static_unit(_x: &'static u32) {}

fn call_take_static_unit() {
    take_static_unit(&GLOBAL)
}

fn take_str(_s: &'static str) {}

fn call_take_str() {
    take_str("hello")
}

/// The loop joins borrows of a global: the static abstraction holding the
/// shared loan of the global gets "demoted" when merged.
fn loop_glob(n: u32) -> u32 {
    let mut r = &GLOBAL;
    let mut i = 0;
    while i < n {
        r = &GLOBAL;
        i += 1;
    }
    *r
}

fn loop_choose<'a>(x: &'a u32, n: u32) -> &'a u32 {
    let mut r = x;
    let mut i = 0;
    while i < n {
        r = &GLOBAL;
        i += 1;
    }
    r
}

fn choose<'a>(b: bool, x: &'a u32, y: &'a u32) -> &'a u32 {
    if b {
        x
    } else {
        y
    }
}

fn loop_choose_call<'a>(x: &'a u32, n: u32) -> &'a u32 {
    let mut r = x;
    let mut i = 0;
    while i < n {
        r = choose(true, r, &GLOBAL);
        i += 1;
    }
    r
}

/// The abstraction introduced by the call to [ret_static_mut] contains a
/// 'static borrow: it can't be demoted and the loop abstraction gets "promoted"
/// to 'static.
fn loop_static_mut(x: &'static mut u32, n: u32) {
    let mut r = x;
    let mut i = 0;
    while i < n {
        r = ret_static_mut(r);
        *r += 1;
        i += 1;
    }
}

/// Regions which outlive 'static are merged with 'static
fn outlives<'a: 'static>(x: &'a u32) -> &'static u32 {
    x
}

fn call_outlives() -> u32 {
    *outlives(&GLOBAL)
}

fn outlives2<'a, 'b: 'static>(x: &'a mut u32, y: &'b u32) -> &'b u32 {
    *x += 1;
    y
}

fn call_outlives2(x: &mut u32) -> u32 {
    *outlives2(x, &GLOBAL)
}

fn outlives_mut<'a: 'static>(x: &'a mut u32) -> &'static mut u32 {
    x
}

fn incr_outlives_mut(x: &'static mut u32) {
    *outlives_mut(x) += 1
}
