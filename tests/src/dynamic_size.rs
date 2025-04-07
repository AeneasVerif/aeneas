//@ [!lean] skip

fn alloc_slice<const N: usize>() -> Box<[u8]> {
    Box::new([0; N])
}

pub struct Wrapper<T: ?Sized> {
    data: T,
}

fn alloc_wrapper<const N: usize>() -> Box<Wrapper<[u8]>> {
    Box::new(Wrapper { data: [0; N] })
}
