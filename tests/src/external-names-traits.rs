//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods -external-names tests/external-names/external-names-traits.json -extra-includes=ExternalNamesModel
//! A trait modelled through a list of external names, whose entry names one
//! of the trait's methods. The models read from a file are trusted, so
//! `-filter-trait-methods` keeps every method of the impl. Here, the impl only
//! has `write_str`: Charon only translates the provided methods that are used.

pub struct Counter {
    pub n: usize,
}

impl core::fmt::Write for Counter {
    fn write_str(&mut self, _s: &str) -> core::fmt::Result {
        self.n = self.n.wrapping_add(1);
        Ok(())
    }
}
