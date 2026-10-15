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

/// 'static borrows hidden inside ADTs (the static region doesn't appear in the
/// signatures)
fn read_static_ref(s: StaticRef) -> u32 {
    *s.x
}

fn read_mk_static_ref() -> u32 {
    read_static_ref(mk_static_ref())
}

fn get_static_ref(s: StaticRef) -> &'static u32 {
    s.x
}

fn read_get_static_ref() -> u32 {
    *get_static_ref(mk_static_ref())
}

fn ref_static_ref<'a>(s: &'a StaticRef) -> &'static u32 {
    s.x
}

fn ref_mut_static_ref<'a>(s: &'a mut StaticRef) {
    s.x = &GLOBAL
}

struct StaticMut {
    x: &'static mut u32,
}

fn incr_hidden_static_mut(s: StaticMut) {
    *s.x += 1
}

fn get_hidden_static_mut(s: StaticMut) -> &'static mut u32 {
    s.x
}

struct Mixed<'a> {
    x: &'a mut u32,
    y: &'static u32,
}

fn use_mixed<'a>(m: Mixed<'a>) {
    *m.x += *m.y
}

fn get_mixed<'a>(m: Mixed<'a>) -> (&'a mut u32, &'static u32) {
    (m.x, m.y)
}

fn call_mixed(x: &mut u32) {
    use_mixed(Mixed { x, y: &GLOBAL })
}

fn call_incr_hidden_static_mut(x: &'static mut u32) {
    incr_hidden_static_mut(StaticMut { x })
}

fn call_get_hidden_static_mut(x: &'static mut u32) {
    *get_hidden_static_mut(StaticMut { x }) += 1
}

fn id_hidden_static_mut(s: StaticMut) -> StaticMut {
    s
}

fn loop_hidden_static_mut(s: StaticMut, n: u32) {
    let mut s = s;
    let mut i = 0;
    while i < n {
        s = id_hidden_static_mut(s);
        *s.x += 1;
        i += 1;
    }
}

fn loop_hidden_static_mut1(x: &'static mut u32, n: u32) {
    let mut r = x;
    let mut i = 0;
    while i < n {
        r = get_hidden_static_mut(StaticMut { x: r });
        *r += 1;
        i += 1;
    }
}

fn branch_hidden_static_mut(s: StaticMut, b: bool) {
    let s = if b { id_hidden_static_mut(s) } else { s };
    *s.x += 1;
}

fn loop_hidden_static_ref(n: u32) -> u32 {
    let mut s = StaticRef { x: &GLOBAL };
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        s = StaticRef { x: &GLOBAL };
        acc += *s.x;
        i += 1;
    }
    acc
}

/// Enumerations containing 'static borrows: matching on them requires
/// reborrowing the 'static part of the symbolic value
fn read_opt_static(o: Option<&'static u32>) -> u32 {
    match o {
        Some(x) => *x,
        None => 0,
    }
}

fn read_opt_static_ref(o: Option<StaticRef>) -> u32 {
    match o {
        Some(s) => *s.x,
        None => 0,
    }
}

struct Outer {
    s: StaticRef,
}

fn read_outer(o: Outer) -> u32 {
    *o.s.x
}

enum StaticEnum {
    A(&'static u32),
    B,
}

fn read_static_enum(e: StaticEnum) -> u32 {
    match e {
        StaticEnum::A(x) => *x,
        StaticEnum::B => 0,
    }
}

enum StaticList {
    Cons(&'static u32, Box<StaticList>),
    Nil,
}

fn static_list_head(l: StaticList) -> u32 {
    match l {
        StaticList::Cons(x, _) => *x,
        StaticList::Nil => 0,
    }
}

/// A common pattern: a structure with a `&'static str` field
struct Named {
    name: &'static str,
    v: u32,
}

fn get_name(n: &Named) -> &'static str {
    n.name
}

fn set_name(n: &mut Named) {
    n.name = "hello";
    n.v += 1
}

fn mk_named() -> Named {
    Named { name: "a", v: 0 }
}

fn use_named() -> u32 {
    let mut n = mk_named();
    set_name(&mut n);
    let _ = get_name(&n);
    n.v
}

pub struct C {
    pub d: &'static usize,
    pub x: usize,
}

pub fn read_c(c: &mut C) -> usize {
    c.x
}

pub fn update_c(c: &mut C) {
    c.x += *c.d
}

pub fn call_read_c(c: &mut C) -> usize {
    read_c(c) + read_c(c)
}

/// Joining/copying symbolic values containing 'static borrows: we need to
/// introduce region abstractions for the static region
fn loop_opt_static(o: Option<&'static u32>, n: u32) -> u32 {
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        match o {
            Some(x) => acc += *x,
            None => {}
        }
        i += 1;
    }
    acc
}

fn branch_opt_static(o: Option<&'static u32>, p: Option<&'static u32>, b: bool) -> u32 {
    let q = if b { o } else { p };
    match q {
        Some(x) => *x,
        None => 0,
    }
}

fn copy_opt_static(o: Option<&'static u32>) -> u32 {
    let a = o;
    let b = o;
    match (a, b) {
        (Some(x), Some(y)) => *x + *y,
        _ => 0,
    }
}

fn dup_opt_static(o: Option<&'static u32>) -> (Option<&'static u32>, Option<&'static u32>) {
    (o, o)
}

#[derive(Clone, Copy)]
struct CopyStaticRef {
    x: &'static u32,
}

fn dup_copy_static_ref(s: CopyStaticRef) -> (CopyStaticRef, CopyStaticRef) {
    (s, s)
}

fn loop_copy_static_ref(s: CopyStaticRef, n: u32) -> u32 {
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        acc += *s.x;
        i += 1;
    }
    acc
}

/// Joining concrete values containing 'static borrows
fn join_concrete_static_ref(b: bool) -> u32 {
    let o: Option<StaticRef> = if b {
        Some(StaticRef { x: &GLOBAL })
    } else {
        None
    };
    match o {
        Some(s) => *s.x,
        None => 0,
    }
}

fn join_concrete_static(b: bool) -> u32 {
    let o: Option<&'static u32> = if b { Some(&GLOBAL) } else { None };
    match o {
        Some(x) => *x,
        None => 0,
    }
}

/// Mutable 'static borrows in enumerations
fn opt_static_mut(o: Option<&'static mut u32>) {
    match o {
        Some(x) => *x += 1,
        None => {}
    }
}

fn branch_opt_static_mut(o: Option<&'static mut u32>, p: Option<&'static mut u32>, b: bool) {
    let q = if b { o } else { p };
    match q {
        Some(x) => *x += 1,
        None => {}
    }
}

/// Copies of values containing 'static borrows inside loops and branches
fn copy_in_loop_static(o: Option<&'static u32>, n: u32) -> Option<&'static u32> {
    let mut i = 0;
    let mut r = None;
    while i < n {
        r = o;
        i += 1;
    }
    r
}

fn copy_in_branch_static(o: Option<&'static u32>, b: bool) -> u32 {
    let mut acc = 0;
    if b {
        let a = o;
        acc = match a {
            Some(x) => *x,
            None => 0,
        };
    }
    acc + match o {
        Some(x) => *x,
        None => 0,
    }
}
