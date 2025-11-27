//@ [!lean] skip

// TODO: #[derive(PartialEq, Eq, Clone, Debug)]
#[derive(Clone)]
enum Enum<T> {
    Variant0,
    Variant1(bool),
    Variant2(u32),
    Variant3(T),
    Variant4(Vec<T>),
}

#[derive(Clone)]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
    // TODO: Vec<...>
}

#[derive(Clone)]
struct Struct<T> {
    f0 : (),
    f1: bool,
    f2: u32,
    f3: T,
    f4: Vec<T>,
}
