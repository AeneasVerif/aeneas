//@ [!borrow-check] aeneas-args=-test-trans-units
//@ [coq,fstar] subdir=misc
//! This module doesn't contain **functions which use nested borrows in their
//! signatures**, and doesn't contain functions with loops.

pub struct Pair<T1, T2> {
    pub x: T1,
    pub y: T2,
}

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// Sometimes, enumerations with one variant are not treated
/// the same way as the other variants (for example, downcasts
/// are not always introduced).
/// A downcast is the cast of an enum to a specific variant, like
/// in the left value of:
/// `((_0 as Right).0: T2) = move _1;`
pub enum One<T1> {
    One(T1),
}

/// Truely degenerate case
/// Instantiations of this are encoded as constant values by rust.
pub enum EmptyEnum {
    Empty,
}

/// Enumeration (several variants with no parameters)
/// Those are not encoded as constant values.
pub enum Enum {
    Variant1,
    Variant2,
}

/// Degenerate struct
/// Instanciations of this are encoded as constant values by rust.
pub struct EmptyStruct {}

pub enum Sum<T1, T2> {
    Left(T1),
    Right(T2),
}

pub fn cast_u32_to_i32(x: u32) -> i32 {
    x as i32
}

pub fn cast_bool_to_i32(x: bool) -> i32 {
    x as i32
}

#[allow(clippy::unnecessary_cast)]
pub fn cast_bool_to_bool(x: bool) -> bool {
    x as bool
}

#[allow(unused_variables)]
pub fn test2() {
    let x: u32 = 23;
    let y: u32 = 44;
    let z = x + y;
    let p: Pair<u32, u32> = Pair { x, y: z };
    let s: Sum<u32, bool> = Sum::Right(true);
    let o: One<u64> = One::One(3);
    let e0 = EmptyEnum::Empty;
    let e1 = e0;
    let enum0 = Enum::Variant1;
}

pub fn get_max(x: u32, y: u32) -> u32 {
    if x >= y {
        x
    } else {
        y
    }
}

pub fn test3() {
    let x = get_max(4, 3);
    let y = get_max(10, 11);
    let z = x + y;
    assert!(z == 15);
}

pub fn test_neg1() {
    let x: i32 = 3;
    let y = -x;
    assert!(y == -3);
}

/// Testing nested references.
pub fn refs_test1() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    **ppx = 1;
    // The interesting thing happening here is that the borrow of x is inside
    // the borrow of px: ending the borrow of x requires ending the borrow of
    // px first.
    assert!(x == 1);
}

pub fn refs_test2() {
    let mut x = 0;
    let mut y = 1;
    let mut px = &mut x;
    let py = &mut y;
    let ppx = &mut px;
    *ppx = py;
    **ppx = 2;
    assert!(*px == 2);
    assert!(x == 0);
    assert!(*py == 2);
    assert!(y == 2);
}

/// Box creation
#[allow(unused_variables)]
pub fn test_list1() {
    let l: List<i32> = List::Cons(0, Box::new(List::Nil));
}

pub fn copy_int(x: i32) -> i32 {
    x
}

/// Just checking the parameters given to unreachable
/// Rk.: the input parameter prevents using the function as a unit test.
pub fn test_unreachable(b: bool) {
    if b {
        unreachable!();
    }
}

/// Rem.: the input parameter prevents using the function as a unit test.
pub fn test_panic(b: bool) {
    if b {
        panic!();
    }
}

/// Just checking the parameters given to panic
/// Rem.: the input parameter prevents using the function as a unit test.
pub fn test_panic_msg(b: bool) {
    if b {
        panic!("Panicked!");
    }
}

// Just testing that shared loans are correctly handled
pub fn test_copy_int() {
    let x = 0;
    let px = &x;
    let y = copy_int(x);
    assert!(*px == y);
}

pub fn is_cons<T>(l: &List<T>) -> bool {
    match l {
        List::Cons(_, _) => true,
        List::Nil => false,
    }
}

pub fn test_is_cons() {
    let l: List<i32> = List::Cons(0, Box::new(List::Nil));

    assert!(is_cons(&l));
}

pub fn split_list<T>(l: List<T>) -> (T, List<T>) {
    match l {
        List::Cons(hd, tl) => (hd, *tl),
        _ => panic!(),
    }
}

#[allow(unused_variables)]
pub fn test_split_list() {
    let l: List<i32> = List::Cons(0, Box::new(List::Nil));

    let (hd, tl) = split_list(l);
    assert!(hd == 0);
}

pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        x
    } else {
        y
    }
}

pub fn choose_test() {
    let mut x = 0;
    let mut y = 0;
    let z = choose(true, &mut x, &mut y);
    *z += 1;
    assert!(*z == 1);
    // drop(z)
    assert!(x == 1);
    assert!(y == 0);
}

/// Test with a char literal - testing serialization
pub fn test_char() -> char {
    'a'
}

/// This triggered a bug at some point
pub fn panic_mut_borrow(_: &mut u32) {
    panic!()
}

/// Mutually recursive types
pub enum Tree<T> {
    Leaf(T),
    Node(T, NodeElem<T>, Box<Tree<T>>),
}

pub enum NodeElem<T> {
    Cons(Box<Tree<T>>, Box<NodeElem<T>>),
    Nil,
}

/*
// TODO: those definitions require semantic termination (breaks the Coq backend
// because we don't use fuel in this case).

/// Mutually recursive functions
pub fn even(x: u32) -> bool {
    if x == 0 {
        true
    } else {
        odd(x - 1)
    }
}

pub fn odd(x: u32) -> bool {
    if x == 0 {
        false
    } else {
        even(x - 1)
    }
}

pub fn test_even_odd() {
    assert!(even(0));
    assert!(even(4));
    assert!(odd(1));
    assert!(odd(5));
}
*/

#[allow(clippy::needless_lifetimes)]
pub fn list_length<'a, T>(l: &'a List<T>) -> u32 {
    match l {
        List::Nil => 0,
        List::Cons(_, l1) => 1 + list_length(l1),
    }
}

#[allow(clippy::needless_lifetimes)]
pub fn list_nth_shared<'a, T>(l: &'a List<T>, i: u32) -> &'a T {
    match l {
        List::Nil => {
            panic!()
        }
        List::Cons(x, tl) => {
            if i == 0 {
                x
            } else {
                list_nth_shared(tl, i - 1)
            }
        }
    }
}

#[allow(clippy::needless_lifetimes)]
pub fn list_nth_mut<'a, T>(l: &'a mut List<T>, i: u32) -> &'a mut T {
    match l {
        List::Nil => {
            panic!()
        }
        List::Cons(x, tl) => {
            if i == 0 {
                x
            } else {
                list_nth_mut(tl, i - 1)
            }
        }
    }
}

/// In-place list reversal - auxiliary function
pub fn list_rev_aux<T>(li: List<T>, mut lo: List<T>) -> List<T> {
    match li {
        List::Nil => lo,
        List::Cons(hd, mut tl) => {
            let next = *tl;
            *tl = lo;
            lo = List::Cons(hd, tl);
            list_rev_aux(next, lo)
        }
    }
}

/// In-place list reversal
#[allow(clippy::needless_lifetimes)]
pub fn list_rev<'a, T>(l: &'a mut List<T>) {
    let li = std::mem::replace(l, List::Nil);
    *l = list_rev_aux(li, List::Nil);
}

pub fn test_list_functions() {
    let mut ls = List::Cons(
        0,
        Box::new(List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))))),
    );
    assert!(list_length(&ls) == 3);
    assert!(*list_nth_shared(&ls, 0) == 0);
    assert!(*list_nth_shared(&ls, 1) == 1);
    assert!(*list_nth_shared(&ls, 2) == 2);
    let x = list_nth_mut(&mut ls, 1);
    *x = 3;
    assert!(*list_nth_shared(&ls, 0) == 0);
    assert!(*list_nth_shared(&ls, 1) == 3); // Updated
    assert!(*list_nth_shared(&ls, 2) == 2);
}

pub fn id_mut_pair1<'a, T1, T2>(x: &'a mut T1, y: &'a mut T2) -> (&'a mut T1, &'a mut T2) {
    (x, y)
}

pub fn id_mut_pair2<'a, T1, T2>(p: (&'a mut T1, &'a mut T2)) -> (&'a mut T1, &'a mut T2) {
    p
}

pub fn id_mut_pair3<'a, 'b, T1, T2>(x: &'a mut T1, y: &'b mut T2) -> (&'a mut T1, &'b mut T2) {
    (x, y)
}

pub fn id_mut_pair4<'a, 'b, T1, T2>(p: (&'a mut T1, &'b mut T2)) -> (&'a mut T1, &'b mut T2) {
    p
}

/// Testing constants (some constants are hard to retrieve from MIR, because
/// they are compiled to very low values).
/// We resort to the following structure to make rustc generate constants...
pub struct StructWithTuple<T1, T2> {
    p: (T1, T2),
}

pub fn new_tuple1() -> StructWithTuple<u32, u32> {
    StructWithTuple { p: (1, 2) }
}

pub fn new_tuple2() -> StructWithTuple<i16, i16> {
    StructWithTuple { p: (1, 2) }
}

pub fn new_tuple3() -> StructWithTuple<u64, i64> {
    StructWithTuple { p: (1, 2) }
}

/// Similar to [StructWithTuple]
pub struct StructWithPair<T1, T2> {
    p: Pair<T1, T2>,
}

pub fn new_pair1() -> StructWithPair<u32, u32> {
    // This actually doesn't make rustc generate a constant...
    // I guess it only happens for tuples.
    StructWithPair {
        p: Pair { x: 1, y: 2 },
    }
}

pub fn test_constants() {
    assert!(new_tuple1().p.0 == 1);
    assert!(new_tuple2().p.0 == 1);
    assert!(new_tuple3().p.0 == 1);
    assert!(new_pair1().p.x == 1);
}

/// This assignment is trickier than it seems
#[allow(unused_assignments)]
pub fn test_weird_borrows1() {
    let mut x = 0;
    let mut px = &mut x;
    // Context:
    // x -> [l0]
    // px -> &mut l0 (0:i32)

    px = &mut (*px);
}

pub fn test_mem_replace(px: &mut u32) {
    let y = std::mem::replace(px, 1);
    assert!(y == 0);
    *px = 2;
}

/// Check that matching on borrowed values works well.
pub fn test_shared_borrow_bool1(b: bool) -> u32 {
    // Create a shared borrow of b
    let _pb = &b;
    // Match on b
    if b {
        0
    } else {
        1
    }
}

/// Check that matching on borrowed values works well.
/// Testing the concrete execution here.
pub fn test_shared_borrow_bool2() -> u32 {
    let b = true;
    // Create a shared borrow of b
    let _pb = &b;
    // Match on b
    if b {
        0
    } else {
        1
    }
}

/// Check that matching on borrowed values works well.
/// In case of enumerations, we need to strip the outer loans before evaluating
/// the discriminant.
pub fn test_shared_borrow_enum1(l: List<u32>) -> u32 {
    // Create a shared borrow of l
    let _pl = &l;
    // Match on l - must ignore the shared loan
    match l {
        List::Nil => 0,
        List::Cons(_, _) => 1,
    }
}

/// Check that matching on borrowed values works well.
/// Testing the concrete execution here.
pub fn test_shared_borrow_enum2() -> u32 {
    let l: List<u32> = List::Nil;
    // Create a shared borrow of l
    let _pl = &l;
    // Match on l - must ignore the shared loan
    match l {
        List::Nil => 0,
        List::Cons(_, _) => 1,
    }
}

pub fn incr(x: &mut u32) {
    *x += 1;
}

pub fn call_incr(mut x: u32) -> u32 {
    incr(&mut x);
    x
}

pub fn read_then_incr(x: &mut u32) -> u32 {
    let r = *x;
    *x += 1;
    r
}

pub struct Tuple<T1, T2>(T1, T2);

pub fn read_tuple(x: &(u32, u32)) -> u32 {
    x.0
}

pub fn update_tuple(x: &mut (u32, u32)) {
    x.0 = 1;
}

pub fn read_tuple_struct(x: &Tuple<u32, u32>) -> u32 {
    x.0
}

pub fn update_tuple_struct(x: &mut Tuple<u32, u32>) {
    x.0 = 1;
}

pub fn create_tuple_struct(x: u32, y: u64) -> Tuple<u32, u64> {
    Tuple(x, y)
}

/// Structure with one field
pub struct IdType<T>(T);

pub fn use_id_type<T>(x: IdType<T>) -> T {
    x.0
}

pub fn create_id_type<T>(x: T) -> IdType<T> {
    IdType(x)
}

pub fn not_bool(x: bool) -> bool {
    !x
}

pub fn not_u32(x: u32) -> u32 {
    !x
}

pub fn not_i32(x: i32) -> i32 {
    !x
}

fn borrow_mut_tuple<T, U>(x: &mut (T, U)) -> &mut (T, U) {
    x
}

// Testing the simplification of the ADT aggregates in the presence of symbolic expansions
mod ExpandSimpliy {
    pub struct Wrapper<T>(T, T);

    pub fn check_expand_simplify_symb1(x: Wrapper<bool>) -> Wrapper<bool> {
        if x.0 {
            x
        } else {
            x
        }
    }

    pub struct Wrapper2 {
        b: bool,
        x: u32,
    }

    pub fn check_expand_simplify_symb2(x: Wrapper2) -> Wrapper2 {
        if x.b {
            x
        } else {
            x
        }
    }
}
