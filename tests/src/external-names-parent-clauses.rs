//@ [lean] known-failure
//@ [!lean] skip
//@ [lean] aeneas-args=-external-names tests/external-names/external-names-parent-clauses.json
//! Checks that a trait entry names all of its parent clauses or none: they are
//! matched by position. Here, `FusedIterator` has one parent clause
//! (`Iterator`), and the entry names two.

pub fn count<I: core::iter::FusedIterator>(it: I) -> usize {
    it.count()
}
