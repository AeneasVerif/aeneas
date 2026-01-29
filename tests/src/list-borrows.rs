//@ [!lean] skip

pub struct LCell<'a> {
    value: &'a mut i32,
    next: List<'a>,
}

pub enum List<'a> {
    Nil,
    Cons(Box<LCell<'a>>),
}
use List::*;

fn cons<'a>(value: &'a mut i32, next: List<'a>) -> List<'a> {
    Cons(Box::new(LCell { value, next }))
}

fn increment_list<'a>(mut l: List<'a>) {
    while let Cons(b) = l {
        *b.value += 1;
        l = (*b).next;
    }
}
