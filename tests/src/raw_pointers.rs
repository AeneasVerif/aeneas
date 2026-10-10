//@ [!lean] skip
//! Raw pointers: reads and writes through pointers derived from borrows, and
//! slices built from raw pointers.

fn read_via_ptr(data: &[u16; 8]) -> u16 {
    unsafe {
        let ptr = data.as_ptr();
        *ptr.add(1)
    }
}

fn write_via_ptr(data: &mut [u16; 8]) {
    unsafe {
        let ptr = data.as_mut_ptr();
        *ptr.add(2) = 42;
    }
}

/// The writes through the pointer are visible once the slice is used again.
fn write_then_read(data: &mut [u32]) -> u32 {
    let p = data.as_mut_ptr();
    unsafe {
        *p = 1;
    }
    data[0]
}

fn local_array() -> u8 {
    let mut a = [0u8; 4];
    let p = a.as_mut_ptr();
    unsafe {
        *p.add(3) = 7;
    }
    a[3]
}

/// Returns a pointer into the slice: the pointer is not valid anymore once the
/// caller uses the slice again.
fn first_ptr(data: &mut [u8]) -> *mut u8 {
    data.as_mut_ptr()
}

unsafe fn write_through(p: *mut u8, v: u8) {
    *p = v;
}

fn swap_through_ptrs(x: &mut [u64]) {
    let p = x.as_mut_ptr();
    unsafe {
        let a = *p;
        let b = *p.add(1);
        *p = b;
        *p.add(1) = a;
    }
}

fn set_via_slice(p: *mut u8, len: usize) {
    let s = unsafe { core::slice::from_raw_parts_mut(p, len) };
    s[0] = 1;
}

fn sum_via_slice(p: *const u8, len: usize) -> u8 {
    let s = unsafe { core::slice::from_raw_parts(p, len) };
    s[0].wrapping_add(s[1])
}

fn boxed() -> u32 {
    let p = Box::into_raw(Box::new(3u32));
    unsafe {
        *p = 4;
        *Box::from_raw(p)
    }
}

fn call_write_through(data: &mut [u8]) {
    let p = data.as_mut_ptr();
    unsafe { write_through(p, 9) };
}

/// The writes through the pointer are visible once the borrow ends.
fn from_mut_write(x: &mut u32) -> u32 {
    let p = core::ptr::from_mut(x);
    unsafe {
        *p = 5;
    }
    *x
}

trait Counter {
    fn next(&self) -> u32;
}

struct PtrCounter {
    p: *mut u32,
}

impl Counter for PtrCounter {
    fn next(&self) -> u32 {
        unsafe {
            let v = *self.p;
            *self.p = v.wrapping_add(1);
            v
        }
    }
}

/// The two calls must not be merged: they read and modify the heap.
fn next_twice<T: Counter>(c: &T) -> u32 {
    let a = c.next();
    let b = c.next();
    a.wrapping_add(b)
}

fn next_once<T: Counter>(c: &T) -> u32 {
    c.next()
}

/// The two calls must not be merged: they (indirectly) modify the heap.
fn next_twice_via_generic<T: Counter>(c: &T) -> u32 {
    let a = next_once(c);
    let b = next_once(c);
    a.wrapping_add(b)
}
