//@ [coq,fstar] subdir=misc
fn main() {
    // This uses the Iterator => IntoIterator blanket impl.
    let _ = (0..1).into_iter();
}
