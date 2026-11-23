//@ [!lean] skip
// A trait method type parameter which only appears in the output type.

pub enum Opt<F> {
    No,
    Yes(F),
}

pub trait Tr {
    fn get<F>(&self) -> Opt<F>;
}

pub fn caller<X: Tr, F>(x: &X) -> u32 {
    match x.get::<F>() {
        Opt::No => 0,
        Opt::Yes(_) => 1,
    }
}

impl Tr for u32 {
    fn get<F>(&self) -> Opt<F> {
        Opt::No
    }
}

pub fn use_impl(x: &u32) -> u32 {
    caller::<u32, u8>(x)
}
