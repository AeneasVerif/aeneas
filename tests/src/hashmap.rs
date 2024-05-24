//! A hashmap implementation.
//!
//! Current limitations:
//! - all the recursive functions should be rewritten with loops, once
//!   we have support for this.
//! - we will need function pointers/closures if we want to make the map
//!   generic in the key type (having function pointers allows to mimic traits)
//! - for the "get" functions: we don't support borrows inside of enumerations
//!   for now, so we can't return a type like `Option<&T>`. The real restriction
//!   we currently have on borrows is that we forbid *nested* borrows in function
//!   signatures, like in `&'a mut &'b mut T` (and the real problem comes from
//!   nested *lifetimes*, not nested borrows). Getting the borrows inside of
//!   enumerations mostly requires to pour some implementation time in it.

use std::vec::Vec;
pub type Key = usize; // TODO: make this generic
pub type Hash = usize;

pub enum List<T> {
    Cons(Key, T, Box<List<T>>),
    Nil,
}

/// A hash function for the keys.
/// Rk.: we use shared references because we anticipate on the generic
/// hash map version.
pub fn hash_key(k: &Key) -> Hash {
    // Do nothing for now, we might want to implement something smarter
    // in the future, or to call an external function (which will be
    // abstract): we don't need to reason about the hash function.
    *k
}

/// A hash map from [u64] to values
pub struct HashMap<T> {
    /// The current number of entries in the table
    num_entries: usize,
    /// The max load factor, expressed as a fraction
    max_load_factor: (usize, usize),
    /// The max load factor applied to the current table length:
    /// gives the threshold at which to resize the table.
    max_load: usize,
    /// The table itself
    slots: Vec<List<T>>,
}

impl<T> HashMap<T> {
    /// Allocate a vector of slots of a given size.
    /// We would need a loop, but can't use loops for now...
    fn allocate_slots(mut slots: Vec<List<T>>, mut n: usize) -> Vec<List<T>> {
        while n > 0 {
            slots.push(List::Nil);
            n -= 1;
        }
        slots
    }

    /// Create a new table, with a given capacity
    fn new_with_capacity(
        capacity: usize,
        max_load_dividend: usize,
        max_load_divisor: usize,
    ) -> Self {
        // TODO: better to use `Vec::with_capacity(capacity)` instead
        // of `Vec::new()`
        let slots = HashMap::allocate_slots(Vec::new(), capacity);
        HashMap {
            num_entries: 0,
            max_load_factor: (max_load_dividend, max_load_divisor),
            max_load: (capacity * max_load_dividend) / max_load_divisor,
            slots,
        }
    }

    pub fn new() -> Self {
        // For now we create a table with 32 slots and a max load factor of 4/5
        HashMap::new_with_capacity(32, 4, 5)
    }

    pub fn clear(&mut self) {
        self.num_entries = 0;
        let slots = &mut self.slots;
        let mut i = 0;
        while i < slots.len() {
            slots[i] = List::Nil;
            i += 1;
        }
    }

    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// Insert in a list.
    /// Return `true` if we inserted an element, `false` if we simply updated
    /// a value.
    fn insert_in_list(key: Key, value: T, mut ls: &mut List<T>) -> bool {
        loop {
            match ls {
                List::Nil => {
                    *ls = List::Cons(key, value, Box::new(List::Nil));
                    return true;
                }
                List::Cons(ckey, cvalue, tl) => {
                    if *ckey == key {
                        *cvalue = value;
                        return false;
                    } else {
                        ls = tl;
                    }
                }
            }
        }
    }

    /// Auxiliary function to insert in the hashmap without triggering a resize
    fn insert_no_resize(&mut self, key: Key, value: T) {
        let hash = hash_key(&key);
        let hash_mod = hash % self.slots.len();
        // We may want to use slots[...] instead of get_mut...
        let inserted = HashMap::insert_in_list(key, value, &mut self.slots[hash_mod]);
        if inserted {
            self.num_entries += 1;
        }
    }

    /// Insertion function.
    /// May trigger a resize of the hash table.
    pub fn insert(&mut self, key: Key, value: T) {
        // Insert
        self.insert_no_resize(key, value);
        // Resize if necessary
        if self.len() > self.max_load {
            self.try_resize()
        }
    }

    /// The resize function, called if we need to resize the table after
    /// an insertion.
    fn try_resize(&mut self) {
        // Check that we can resize: we need to check that there are no overflows.
        // Note that we are conservative about the usize::MAX.
        // Also note that `as usize` is a trait, but we apply it to a constant
        // here, which gets compiled by the MIR interpreter (so we don't see
        // the conversion, actually).
        // Rk.: this is a hit heavy...
        let max_usize = u32::MAX as usize;
        let capacity = self.slots.len();
        // Checking that there won't be overflows by using the fact that, if m > 0:
        // n * m <= p <==> n <= p / m
        let n1 = max_usize / 2;
        if capacity <= n1 / self.max_load_factor.0 {
            // Create a new table with a higher capacity
            let mut ntable = HashMap::new_with_capacity(
                capacity * 2,
                self.max_load_factor.0,
                self.max_load_factor.1,
            );

            // Move the elements to the new table
            HashMap::move_elements(&mut ntable, &mut self.slots, 0);

            // Replace the current table with the new table
            self.slots = ntable.slots;
            self.max_load = ntable.max_load;
        }
    }

    /// Auxiliary function called by [try_resize] to move all the elements
    /// from the table to a new table
    fn move_elements<'a>(ntable: &'a mut HashMap<T>, slots: &'a mut Vec<List<T>>, mut i: usize) {
        while i < slots.len() {
            // Move the elements out of the slot i
            let ls = std::mem::replace(&mut slots[i], List::Nil);
            // Move all those elements to the new table
            HashMap::move_elements_from_list(ntable, ls);
            // Do the same for slot i+1
            i += 1;
        }
    }

    /// Auxiliary function.
    fn move_elements_from_list(ntable: &mut HashMap<T>, mut ls: List<T>) {
        // As long as there are elements in the list, move them
        loop {
            match ls {
                List::Nil => return, // We're done
                List::Cons(k, v, tl) => {
                    // Insert the element in the new table
                    ntable.insert_no_resize(k, v);
                    // Move the elements out of the tail
                    ls = *tl;
                }
            }
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    pub fn contains_key(&self, key: &Key) -> bool {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::contains_key_in_list(key, &self.slots[hash_mod])
    }

    /// Returns `true` if the list contains a value for the specified key.
    pub fn contains_key_in_list(key: &Key, mut ls: &List<T>) -> bool {
        loop {
            match ls {
                List::Nil => return false,
                List::Cons(ckey, _, tl) => {
                    if *ckey == *key {
                        return true;
                    } else {
                        ls = tl;
                    }
                }
            }
        }
    }

    /// We don't support borrows inside of enumerations for now, so we
    /// can't return an option...
    /// TODO: add support for that
    fn get_in_list<'a, 'k>(key: &'k Key, mut ls: &'a List<T>) -> &'a T {
        loop {
            match ls {
                List::Nil => panic!(),
                List::Cons(ckey, cvalue, tl) => {
                    if *ckey == *key {
                        return cvalue;
                    } else {
                        ls = tl;
                    }
                }
            }
        }
    }

    pub fn get<'a, 'k>(&'a self, key: &'k Key) -> &'a T {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::get_in_list(key, &self.slots[hash_mod])
    }

    pub fn get_mut_in_list<'a, 'k>(mut ls: &'a mut List<T>, key: &'k Key) -> &'a mut T {
        while let List::Cons(ckey, cvalue, tl) = ls {
            if *ckey == *key {
                return cvalue;
            } else {
                ls = tl;
            }
        }
        panic!()
    }

    /// Same remark as for [get].
    pub fn get_mut<'a, 'k>(&'a mut self, key: &'k Key) -> &'a mut T {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::get_mut_in_list(&mut self.slots[hash_mod], key)
    }

    /// Remove an element from the list.
    /// Return the removed element.
    fn remove_from_list(key: &Key, mut ls: &mut List<T>) -> Option<T> {
        loop {
            match ls {
                List::Nil => return None,
                // We have to use a guard and split the Cons case into two
                // branches, otherwise the borrow checker is not happy.
                List::Cons(ckey, _, _) if *ckey == *key => {
                    // We have to move under borrows, so we need to use
                    // [std::mem::replace] in several steps.
                    // Retrieve the tail
                    let mv_ls = std::mem::replace(ls, List::Nil);
                    match mv_ls {
                        List::Nil => unreachable!(),
                        List::Cons(_, cvalue, tl) => {
                            // Make the list equal to its tail
                            *ls = *tl;
                            // Return the dropped value
                            return Some(cvalue);
                        }
                    }
                }
                List::Cons(_, _, tl) => {
                    ls = tl;
                }
            }
        }
    }

    /// Same remark as for [get].
    pub fn remove(&mut self, key: &Key) -> Option<T> {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();

        let x = HashMap::remove_from_list(key, &mut self.slots[hash_mod]);
        match x {
            Option::None => Option::None,
            Option::Some(x) => {
                self.num_entries -= 1;
                Option::Some(x)
            }
        }
    }
}

/// I currently can't retrieve functions marked with the attribute #[test],
/// while I want to extract the unit tests and use the normalize on them,
/// so I have to define the test functions somewhere and call them from
/// a test function.
/// TODO: find a way to do that.
#[allow(dead_code)]
fn test1() {
    let mut hm: HashMap<u64> = HashMap::new();
    hm.insert(0, 42);
    hm.insert(128, 18);
    hm.insert(1024, 138);
    hm.insert(1056, 256);
    // Rk.: `&128` introduces a ref constant value
    // TODO: add support for this
    // Rk.: this only happens if we query the MIR too late (for instance,
    // the optimized MIR). It is not a problem if we query, say, the
    // "built" MIR.
    let k = 128;
    assert!(*hm.get(&k) == 18);
    let k = 1024;
    let x = hm.get_mut(&k);
    *x = 56;
    assert!(*hm.get(&k) == 56);
    let x = hm.remove(&k);
    // If we write `x == Option::Some(56)` rust introduces
    // a call to `core::cmp::PartialEq::eq`, which is a trait
    // I don't support for now.
    // Also, I haven't implemented support for `unwrap` yet...
    match x {
        Option::None => panic!(),
        Option::Some(x) => assert!(x == 56),
    };
    let k = 0;
    assert!(*hm.get(&k) == 42);
    let k = 128;
    assert!(*hm.get(&k) == 18);
    let k = 1056;
    assert!(*hm.get(&k) == 256);
}

#[test]
fn tests() {
    test1();
}
