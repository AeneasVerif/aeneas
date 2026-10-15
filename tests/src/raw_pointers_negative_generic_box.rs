//@ [!lean] skip
//@ [lean] known-failure
//! Instantiating a generic function accessing the heap with a box type is
//! rejected (the generic function may cast pointers).

pub unsafe fn read<T>(p: *const T) -> T {
    p.read()
}

pub unsafe fn f(p: *const Box<u32>) -> u32 {
    *read(p)
}
