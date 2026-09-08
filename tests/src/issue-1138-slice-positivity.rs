//@ [coq,fstar] skip
// Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1138
// Using arrays, slices, and vectors should play nicely with datatype positivity

enum E1 {
    V([Box<E1>; 1]),
}

enum E2 {
    V(Vec<E2>),
}

enum E3 {
    V(&'static [E3]),
}
