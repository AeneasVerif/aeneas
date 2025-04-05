//@ [fstar,coq] subdir=misc
fn main() {
    let n = 10.min(1);
    assert!(n == 1);
}
