//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/1141

fn f(g: impl Fn(&())) {
    let _ = g;
}
