//@ [coq,fstar] subdir=misc
pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

fn foo(v: &List<List<u8>>) {
    if let List::Cons(_, t) = v {
        let mut t = &**t;
        while let List::Cons(_, tt) = t {
            t = &**tt;
        }
    }
}
