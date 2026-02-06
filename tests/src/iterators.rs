//@ [!lean] skip
// TODO: rev, take

fn iter_range() {
    for _ in 0..(32usize) {}
}

fn iter_range_step_by(n: usize) {
    for _ in (0..n).step_by(2) {}
}

fn slice_iter_mut_while(b: bool, s: &mut [u16]) {
    let mut it = s.iter_mut();
    while let Some(_) = it.next() {
        while b {}
    }
}

fn slice_iter_while(b: bool, s: &[u16]) {
    let mut it = s.iter();
    while let Some(_) = it.next() {
        while b {}
    }
}

/*
fn array_into_iter<const N : usize>(s : &[u8; N]) {
    for _ in s {}
}

fn array_iter<const N : usize>(s : &[u8; N]) {
    for _ in s.iter() {}
}

fn array_iter_mut<const N : usize>(s : &mut [u8; N]) {
    for _ in s.iter_mut() {}
}

fn slice_into_iter(s : &[u8]) {
    for _ in s {}
}

fn slice_iter(s : &[u8]) {
    for _ in s {}
}

fn slice_iter_mut(s : &mut [u8]) {
    for _ in s.iter_mut() {}
}
*/

/*
fn iter_chunks_take(data : &[u8]) {
    for _ in data.chunks_exact(8).take(32) {}
}
*/
