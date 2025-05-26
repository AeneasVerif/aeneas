//@ charon-args=--rustc-arg=-Zpolonius
//@ [!borrow-check] aeneas-args=-test-trans-units
//@ [coq,fstar] subdir=misc
#![allow(dead_code)]

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// An example which comes from the b-epsilon tree.
///
/// Returns a mutable borrow to the first portion of the list where we
/// can find [x]. This allows to do in-place modifications (insertion, filtering)
/// in a natural manner (this piece of code was inspired by the C++ BeTree).
pub fn get_list_at_x<'a>(ls: &'a mut List<u32>, x: u32) -> &'a mut List<u32> {
    match ls {
        List::Nil => {
            // We reached the end: just return it
            ls
        }
        List::Cons(hd, tl) => {
            if *hd == x {
                ls // Doing this requires NLL
            } else {
                get_list_at_x(tl, x)
            }
        }
    }
}
