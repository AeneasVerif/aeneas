//@ [!lean] skip
//! Enum variant constructors used as function values (`FnOnce`).

pub enum Change {
    Insert(usize),
    Remove(usize),
    Reset,
}

pub fn inserted(items: &[u32]) -> Option<Change> {
    items.iter().position(|x| *x == 0).map(Change::Insert)
}

pub fn removed(at: Option<usize>) -> Option<Change> {
    at.map(Change::Remove)
}

pub fn reset_all(at: Option<usize>) -> Option<Change> {
    at.map(|_| Change::Reset)
}
