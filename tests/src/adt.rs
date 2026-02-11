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
