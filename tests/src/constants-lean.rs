//@ [!lean] skip

trait Params {
    const N: usize;
    const M: usize;
}

fn use_params<P: Params>(n: usize) -> bool {
    &n == &(P::N * P::M)
}

const N : usize = 3;
const M : usize = 4;
const NM : usize = N * M;

struct Wrapper<const N : usize, const M : usize>([u8; N], [u8; N]);

impl<const N : usize, const M : usize> Wrapper<N, M> {
    const NM : usize = N * M;
}

trait Trait {
    const NM : usize;
}

impl<const N : usize, const M : usize> Trait for Wrapper<N, M> {
    const NM : usize = N * M;
}

trait Trait1 {
    const N : usize;
    const M : usize;
    const NM : usize = Self::N * Self::M;
}

impl Trait1 for bool {
    const N : usize = 0;
    const M : usize = 1;
}
