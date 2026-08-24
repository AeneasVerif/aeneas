//@ [!lean] skip

trait Params {
    const N: usize;
    const M: usize;
}

fn use_params<P: Params>(n: usize) -> bool {
    &n == &(P::N * P::M)
}

const N: usize = 3;
const M: usize = 4;
const NM: usize = N * M;

struct Wrapper<const N: usize, const M: usize>([u8; N], [u8; N]);

impl<const N: usize, const M: usize> Wrapper<N, M> {
    const NM: usize = N * M;
}

trait Trait {
    const NM: usize;
}

impl<const N: usize, const M: usize> Trait for Wrapper<N, M> {
    const NM: usize = N * M;
}

trait Trait1 {
    const N: usize;
    const M: usize;
    const NM: usize = Self::N * Self::M;
}

impl Trait1 for bool {
    const N: usize = 0;
    const M: usize = 1;
}

trait Params1 {
    const N: usize;
    const LOGQ: usize;

    const PACKED_LEN: usize = (Self::N * Self::LOGQ) / 8;
    const CT1_LEN: usize = Self::PACKED_LEN;
}

// Non-failing globals must not be lifted to the error monad: chaining more than
// two pure binary operations introduces an intermediate let-binding, which used
// to be turned into a monadic let-binding even though the global is pure.
const FEATURE_A: u32 = 0x02;
const FEATURE_B: u32 = 0x08;
const FEATURE_C: u32 = 0x20;

const TWO_FEATURES: u32 = FEATURE_A | FEATURE_B;
const THREE_FEATURES: u32 = FEATURE_A | FEATURE_B | FEATURE_C;
