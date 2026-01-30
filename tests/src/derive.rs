//@ [!lean] skip

// TODO: #[derive(Debug)]

#[derive(Debug)]
enum ScalarEnum {
    Variant0 = 2,
    Variant1 = 4,
    Variant2 = 8,
    Variant3 = 16,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CopyEnum<T> {
    Variant0,
    Variant1(bool),
    Variant2(u32),
    Variant3(T),
}

#[derive(Clone, PartialEq, Eq)]
enum Enum<T> {
    Variant0,
    Variant1(bool),
    Variant2(u32),
    Variant3(T),
    Variant4(Vec<T>),
}

#[derive(Clone, PartialEq, Eq)]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
    // TODO: Vec<...>
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct CopyStruct<T> {
    f0: (),
    f1: bool,
    f2: u32,
    f3: T,
}

#[derive(Clone, PartialEq, Eq)]
struct Struct<T> {
    f: Vec<T>,
}
