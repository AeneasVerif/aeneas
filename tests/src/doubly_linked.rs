//@ [!lean] skip
//@ charon-args=--opaque=crate::ext
//@ [lean] subdir=DoublyLinked
//@ [lean] aeneas-args=-split-files -all-computable -loops-to-rec

// Keep one extraction namespace and opaque boundary while separating the APIs.
include!("doubly_linked/raw.rs");
include!("doubly_linked/safe.rs");

#[cfg(test)]
#[path = "doubly_linked/tests.rs"]
mod tests;
