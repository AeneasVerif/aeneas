//@ [!lean] skip

struct Struct {
    len: usize,
}

impl Struct {
    fn len(&self) -> usize {
        self.len
    }
    fn f() {}
}

struct BigStructName();

// Checking formatting of the generated code
struct BigStruct(
    BigStructName,
    BigStructName,
    BigStructName,
    BigStructName,
    BigStructName,
    BigStructName,
);
