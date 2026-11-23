//@ [!lean] skip
//! A derived `PartialEq` on an enum whose variant payload holds a `&'static` reference,
//! and a `match` on a shared reference to such an enum.
pub struct Row {
    pub id: u32,
}

impl PartialEq for Row {
    fn eq(&self, other: &Row) -> bool {
        self.id == other.id
    }
}

#[derive(PartialEq)]
pub struct Rf(pub &'static Row);

#[derive(PartialEq)]
pub enum E {
    P { t: Rf },
    Bite,
}

pub fn same(a: &E, b: &E) -> bool {
    a == b
}

pub enum F {
    P(&'static Row),
    Bite,
}

/// Reads through the `&'static` after a `match` on a shared reference.
pub fn id_of(x: &F) -> u32 {
    match x {
        F::P(p) => p.id,
        F::Bite => 0,
    }
}
