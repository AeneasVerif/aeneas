//@ [!lean] skip

fn call_fn_no_state(i: u32) -> u32 {
    let incr = |i: u32| -> u32 { i + 1 };
    incr(i)
}

fn call_fn_shared(a: &[u8], i: usize) -> u8 {
    let read = |i: usize| -> u8 { a[i] };
    read(i)
}

// TODO: monomorphisation in Charon
/*
fn call_fn_mut(a: &mut [u8], i: usize) {
    let mut write = |i: usize| { a[i] = 0 };
    write(i)
}
*/

// TODO: https://github.com/AeneasVerif/charon/issues/989
fn call_fn_parameters<T: Clone>(x: &T) {
    let y = x.clone();
    let consume = |x: T| {};
}
