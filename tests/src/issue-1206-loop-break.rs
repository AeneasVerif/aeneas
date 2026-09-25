//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/1206

pub fn first_nonzero(xs: &[u8]) -> usize {
    let mut idx = xs.len();
    for i in 0..xs.len() {
        if xs[i] != 0 {
            idx = i;
            break;
        }
    }
    idx
}
