//@ charon-args=--opaque=hashmap_utils
//@ aeneas-args=-state -split-files
//@ [coq] aeneas-args=-use-fuel
//@ [fstar] aeneas-args=-decreases-clauses -template-clauses
// Possible to add `--no-code-duplication` if we use the optimized MIR
// TODO: reactivate -test-trans-units
mod hashmap;
mod hashmap_utils;

use crate::hashmap::*;
use crate::hashmap_utils::*;

pub fn insert_on_disk(key: Key, value: u64) {
    // Deserialize
    let mut hm = deserialize();
    // Update
    hm.insert(key, value);
    // Serialize
    serialize(hm);
}

pub fn main() {}
