//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

struct Struct(u32);

enum Enum {
    Unit,
    Tuple(u32),
}

fn make_tuple_struct_with_constructor<T>(x: Option<u32>) -> Option<Struct> {
    x.map(Struct)
}

fn make_enum_with_constructor(x: Option<u32>) -> Option<Enum> {
    x.map(Enum::Tuple)
}

#[verify::test]
fn test_tuple_struct_constructor() {
    let _ = Struct(42);
}

#[verify::test]
fn test_enum_constructor() {
    let _ = Enum::Tuple(42);
}
