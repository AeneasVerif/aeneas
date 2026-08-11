//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::opaque]
struct Wrapper<'a, T>(&'a mut T);

impl<'a, T> Wrapper<'a, T> {
    fn id(self) -> Self {
        self
    }
}

#[verify::opaque]
pub struct WrapperRaw<'a, T> {
    x: *mut T,
    len: usize,
    _phantom: std::marker::PhantomData<&'a mut T>,
}

impl<'a, T> WrapperRaw<'a, T> {
    fn id(self) -> Self {
        self
    }
}
