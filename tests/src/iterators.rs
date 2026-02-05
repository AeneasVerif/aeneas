//@ [!lean] skip

fn test_iter() {
    for _ in 0..(32usize) {}
}

/*fn test_iter1(n: usize) {
    for x in 0..n {}
}*/

/*fn test_shared(a: &[u8]) {
    for _ in a {}
}*/

fn test_step_by(n: usize) {
    for _ in (0..n).step_by(2) {}
}

// TODO: rev, take


/*
fn f<'a>(a: &'a mut [u8], b: &'a [u8]) {
    for _ in a.iter_mut().zip(b.iter()) {}
}
*/
