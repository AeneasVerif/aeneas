//@ [!lean] skip

// A user-defined trait used with a higher-ranked bound.
trait RefTrait<X> {
    fn get(&self) -> X;
}

// Explicit higher-ranked trait bound on a user trait
fn use_higher_ranked_trait_bound<P: for<'a> RefTrait<&'a u8>>(p: &P) -> u8 {
    *p.get()
}

// Same, but written with a `where` clause.
fn use_higher_ranked_trait_bound_where<P>(p: &P) -> u8
where
    P: for<'a> RefTrait<&'a u8>,
{
    *p.get()
}

fn call_fn_ref(g: impl Fn(&u8) -> u8, x: u8) -> u8 {
    g(&x);
    g(&x)
}

fn call_fnmut_ref(mut g: impl FnMut(&u8), x: u8) {
    g(&x);
    g(&x)
}

/*
// TODO
fn call_fnmut_mut_ref(mut g: impl FnMut(&mut u8), x: &mut u8) {
    g(x);
    g(x)
}*/

// `impl FnOnce(&_) -> _`.
fn call_fnonce_ref(g: impl FnOnce(&u8) -> u8, x: u8) -> u8 {
    g(&x)
}

// Higher-ranked bound where the lifetime appears in several argument positions.
fn call_fn_two_refs(g: impl Fn(&u8, &u8) -> u8, x: u8, y: u8) -> u8 {
    g(&x, &y)
}

// A function taking a higher-ranked `Fn` and a value, never calling it.
fn ignore_higher_ranked_fn(_g: impl Fn(&())) {}
