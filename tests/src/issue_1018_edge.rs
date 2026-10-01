//@ [!lean] skip

// More aggressive edge cases for the type-annotation pass.

// (E1) Recursive enum with type param, bare unit variant in a deep
// position.
pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

pub fn list_is_nil<T>(l: &List<T>) -> bool {
    matches!(l, List::Nil)
}

pub fn test_nested_nil() -> bool {
    let l: List<u8> = List::Nil;
    list_is_nil(&l)
}

// (E2) Multiple type parameters, one unit variant.
pub enum Either<A, B> {
    Left(A),
    Right(B),
    Neither,
}

pub fn either_is_neither<A, B>(e: &Either<A, B>) -> bool {
    matches!(e, Either::Neither)
}

pub fn test_two_params() -> bool {
    let e: Either<u8, bool> = Either::Neither;
    either_is_neither(&e)
}

// (E3) Const generic — make sure my fix doesn't accidentally
// annotate based on a const generic alone with no type params.
pub struct Wrap<const N: usize>;

pub fn use_wrap<const N: usize>(_w: &Wrap<N>) -> bool {
    true
}

pub fn test_const_generic() -> bool {
    let w: Wrap<4> = Wrap;
    use_wrap(&w)
}

// (E4) Nested generic: `Some(None)` where the outer return type
// fully constrains. Should not get annotation.
pub fn return_some_none() -> Option<Option<u8>> {
    Some(None)
}

// (E5) Nested generic: pass `Some(None)` where the outer can't infer
// inner. The outer Some's type can be inferred from the outer arg's
// expected type, but the inner None's type cannot.
pub fn outer_takes_opt_opt<T>(_x: Option<Option<T>>) -> bool {
    true
}

pub fn test_nested_some_none() -> bool {
    outer_takes_opt_opt::<u8>(Some(None))
}

// (E6) Empty unit struct — should not be annotated (no type params).
pub struct Unit0;

pub fn use_unit0(_u: &Unit0) -> bool {
    true
}

pub fn test_unit_struct() -> bool {
    let u = Unit0;
    use_unit0(&u)
}

// (E7) Bare value that's a function call returning an Option (not an
// AdtCons), then is_none'd. Should not be affected by my fix.
pub fn make_none<T>() -> Option<T> {
    None
}

pub fn test_via_fun_call() -> bool {
    make_none::<u8>().is_none()
}
