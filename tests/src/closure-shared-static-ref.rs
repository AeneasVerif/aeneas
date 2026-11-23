//@ [!lean] skip
//! A closure capturing a shared slice of values that hold a `&'static` reference.
pub struct Row {
    pub id: u32,
}

pub struct Card {
    pub r: &'static Row,
}

pub fn f(cards: &[Card], index: usize) -> Option<usize> {
    (0..index).fold(
        None,
        move |n, at| if cards[at].r.id == 1 { Some(at) } else { n },
    )
}

pub fn g(cards: &[Card], at: usize) -> bool {
    cards[at].r.id == 1
}
