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

// Regression tests: types which hide a 'static borrow (in an ADT) used in
// combination with the `?` operator, other regions, raw pointers, etc.
pub struct WithStaticRef(pub &'static str);

pub fn question_mark_static_ref(r: Result<u32, WithStaticRef>) -> Result<u32, WithStaticRef> {
    Ok(r?)
}

pub enum StaticError {
    Decode,
    InvalidParams(&'static str),
}

fn static_error_parse(x: u32) -> Result<u32, StaticError> {
    if x == 0 {
        Err(StaticError::Decode)
    } else {
        Ok(x)
    }
}

pub fn static_error_question_mark(x: u32) -> Result<u32, StaticError> {
    let y = static_error_parse(x)?;
    Ok(y)
}

pub fn static_error_match(x: u32) -> Result<u32, StaticError> {
    match static_error_parse(x) {
        Ok(y) => Ok(y),
        Err(e) => Err(e),
    }
}

pub fn static_error_with_region<'a>(
    r: Result<&'a u8, WithStaticRef>,
) -> Result<&'a u8, WithStaticRef> {
    r
}

pub fn static_error_with_mut_region<'a>(
    r: Result<&'a mut u8, WithStaticRef>,
) -> Result<&'a mut u8, WithStaticRef> {
    r
}

pub fn static_error_shared_ret<'a>(x: &'a u32, b: bool) -> Result<&'a u32, StaticError> {
    if b {
        Err(StaticError::InvalidParams("bad"))
    } else {
        Ok(x)
    }
}

pub fn static_error_outlives<'a, 'b: 'a>(r: Result<&'a u8, &'b u8>) -> Result<&'a u8, &'b u8> {
    r
}

pub fn static_error_raw_ptr(
    r: Result<*const u8, WithStaticRef>,
) -> Result<*const u8, WithStaticRef> {
    r
}

// Calling functions whose signature uses the static region (hidden in an ADT)
// together with other regions, inside loops
fn static_error_get<'a>(v: &'a [u8], i: usize) -> Result<&'a u8, StaticError> {
    if i < v.len() {
        Ok(&v[i])
    } else {
        Err(StaticError::Decode)
    }
}

pub fn static_error_loop_question_mark(v: &[u8], n: usize) -> Result<u32, StaticError> {
    let mut i = 0;
    let mut s = 0u32;
    while i < n {
        s += *static_error_get(v, i)? as u32;
        i += 1;
    }
    Ok(s)
}

pub fn static_error_loop_call<'a>(
    mut r: Result<&'a u8, WithStaticRef>,
    n: u32,
) -> Result<&'a u8, WithStaticRef> {
    let mut i = 0;
    while i < n {
        r = static_error_with_region(r);
        i += 1;
    }
    r
}

// The static region (hidden in an ADT) living under borrows of other regions:
// the static region group must still depend on the other region groups
pub struct CtxWithStaticRef {
    pub name: &'static str,
    pub v: u32,
}

pub fn ctx_with_static_ref_get_v(c: &mut CtxWithStaticRef) -> &mut u32 {
    &mut c.v
}

pub fn swap_with_static_ref<'a>(x: &'a mut WithStaticRef, y: &'a mut WithStaticRef) {
    core::mem::swap(x, y)
}

pub fn shared_ref_static_error<'a>(
    r: &'a Result<u32, StaticError>,
) -> &'a Result<u32, StaticError> {
    r
}

// The static region hidden in the type arguments of an ADT with region
// parameters
pub struct MutRefWrapper<'a, T>(pub &'a mut T);

pub fn mut_ref_wrapper_get_v<'a>(c: MutRefWrapper<'a, CtxWithStaticRef>) -> &'a mut u32 {
    &mut c.0.v
}

// Static borrows coerced to borrows with shorter lifetimes
pub fn shorten_static_str<'b>(s: &'static str) -> &'b str {
    s
}

pub fn pick_static_ref<'a>(x: &'a str, w: WithStaticRef, b: bool) -> &'a str {
    if b {
        x
    } else {
        w.0
    }
}

pub fn write_static_ref<'a, 'b>(x: &'a mut (&'b str, u32), s: WithStaticRef) -> &'a mut u32 {
    x.0 = s.0;
    &mut x.1
}
