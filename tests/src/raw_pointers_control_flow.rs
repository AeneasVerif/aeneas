//@ [!lean] skip
//! Raw pointers and control flow.
//!
//! Remark: Aeneas ends the borrows converted to raw pointers lazily, but in a
//! conservative manner: once such a borrow ends, the memory the raw pointer
//! points to is freed, and the model fails if we access it. This happens in
//! particular when entering a loop (see [write_loop]), or when the original
//! borrow is used again.

fn write_if(data: &mut [u8], b: bool) {
    let p = data.as_mut_ptr();
    unsafe {
        if b {
            *p = 1;
        } else {
            *p = 2;
        }
    }
    data[0] = data[0] + 1;
}

/// The model always fails if [n > 0]: the borrow converted to a raw pointer
/// ends before entering the loop.
fn write_loop(data: &mut [u8], n: usize) {
    let p = data.as_mut_ptr();
    let mut i = 0;
    while i < n {
        unsafe {
            *p.add(i) = 0;
        }
        i += 1;
    }
}

fn view_in_loop(data: &mut [u8], n: usize) {
    let mut i = 0;
    while i < n {
        let p = data.as_mut_ptr();
        unsafe {
            *p.add(i) = 0;
        }
        i += 1;
    }
}

fn slice_in_branch(p: *mut u8, b: bool) {
    let s = unsafe { core::slice::from_raw_parts_mut(p, 2) };
    if b {
        s[0] = 1;
    } else {
        s[1] = 1;
    }
}

/// A slice created from a pointer to a local variable. The slice is given back
/// as soon as it is dead, before the borrow converted to a raw pointer ends.
fn local_view() -> u32 {
    let mut a = [0u32; 2];
    let p = a.as_mut_ptr();
    let s = unsafe { core::slice::from_raw_parts_mut(p, 2) };
    s[0] = 5;
    0
}
