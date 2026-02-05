//@ [!lean] skip
// TODO: rev, take

fn test_iter_range() {
    for _ in 0..(32usize) {}
}

fn test_iter_range_step_by(n: usize) {
    for _ in (0..n).step_by(2) {}
}

/*
fn test_array<const N : usize>(s : &[u8; N]) {
    for _ in s {}
}

fn test_array_iter<const N : usize>(s : &[u8; N]) {
    for _ in s.iter() {}
}

fn test_array_iter_mut<const N : usize>(s : &mut [u8; N]) {
    for _ in s.iter_mut() {}
}

fn test_slice(s : &[u8]) {
    for _ in s {}
}

fn test_slice_iter(s : &[u8]) {
    for _ in s {}
}

fn test_slice_iter_mut(s : &mut [u8]) {
    for _ in s.iter_mut() {}
}
*/

/*
fn test_iter_chunks_take(data : &[u8]) {
    for _ in data.chunks_exact(8).take(32) {}
}
*/
