//@ [!lean] skip

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum CopyEnumOneVariant {
    Variant(bool),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ScalarEnum {
    Variant0 = 2,
    Variant1 = 4,
    Variant2 = 8,
    Variant3 = 16,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum CopyEnum<T> {
    Variant0,
    Variant1(bool),
    Variant2(u32),
    Variant3(T),
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Enum<T> {
    Variant0,
    Variant1(bool),
    Variant2(u32),
    Variant3(T),
    Variant4(Vec<T>),
}

// TODO: add Debug
#[derive(Clone, PartialEq, Eq)]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
    // TODO: Vec<...>
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct CopyStruct<T> {
    f0: (),
    f1: bool,
    f2: u32,
    f3: T,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Struct<T> {
    f: Vec<T>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Struct6Fields {
    a: u32,
    b: u32,
    c: u32,
    d: u32,
    e: u32,
    f: u32,
}
