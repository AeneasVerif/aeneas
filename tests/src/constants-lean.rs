//@ [!lean] skip

trait Params {
    const N: usize;
    const M: usize;
}

fn use_params<P: Params>(n: usize) {
    debug_assert_eq!(n, P::N * P::M);
}
