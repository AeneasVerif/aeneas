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
