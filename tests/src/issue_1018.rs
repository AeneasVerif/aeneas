//@ [!lean] skip

// Reproducer for issue #1018: type information getting lost when
// a bare zero-argument ADT constructor (e.g. `None`) flows into a
// function whose type parameter cannot be inferred from context.

// (1) The original bug from the issue. After inlining, the bare
//     `None` reaches `is_none` whose type parameter cannot be
//     inferred from its return type (`bool`).
pub fn test_is_none() -> bool {
    let x: Option<u8> = None;
    x.is_none()
}

// (2) Same shape, but with `is_some`.
pub fn test_is_some() -> bool {
    let x: Option<u8> = None;
    x.is_some()
}

// (3) Returning `None` directly: the expected type is fully concrete,
//     so no annotation should be needed.
pub fn test_return_none() -> Option<u8> {
    None
}

// (4) Nested: `Some(None)` where the inner None's type parameter
//     would normally be inferred from the outer Some. The expected
//     return type fully constrains everything.
pub fn test_some_none() -> Option<Option<u8>> {
    Some(None)
}

// (5) A custom unit-like enum variant with a type parameter.
pub enum MyEnum<T> {
    A,
    B(T),
}

pub fn use_my_enum<T>(_x: &MyEnum<T>) -> bool {
    true
}

pub fn test_custom_unit_variant() -> bool {
    let x: MyEnum<u8> = MyEnum::A;
    use_my_enum(&x)
}

// (6) Result::Err with a unit value. The Ok type parameter cannot
//     be inferred from the input alone.
pub fn check_err<T>(r: Result<T, ()>) -> bool {
    r.is_err()
}

pub fn test_result_err() -> bool {
    let x: Result<u8, ()> = Err(());
    check_err(x)
}

// (7) Passing `None` through a tuple into a function that
//     destructures it.
pub fn fst_is_none<T>(p: (bool, Option<T>)) -> bool {
    p.1.is_none()
}

pub fn test_tuple_none() -> bool {
    let p: (bool, Option<u8>) = (true, None);
    fst_is_none(p)
}

// (8) Same shape as (1), but the option lives in a struct
// (forces the AdtCons to flow into a struct field constructor).
pub struct Holder<T> {
    pub value: Option<T>,
}

pub fn holder_is_none<T>(h: &Holder<T>) -> bool {
    h.value.is_none()
}

pub fn test_holder() -> bool {
    let h: Holder<u8> = Holder { value: None };
    holder_is_none(&h)
}
