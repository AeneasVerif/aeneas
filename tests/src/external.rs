//@ charon-args=--no-code-duplication
//@ [!borrow-check] aeneas-args=-state -split-files
//@ [!borrow-check] aeneas-args=-test-trans-units
//@ [coq,fstar] subdir=misc
//! This module uses external types and functions

use std::cell::Cell;

pub fn use_get(rc: &Cell<u32>) -> u32 {
    rc.get()
}

pub fn incr(rc: &mut Cell<u32>) {
    *rc.get_mut() += 1;
}
