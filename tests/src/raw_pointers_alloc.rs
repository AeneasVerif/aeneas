//@ [!lean] skip
//! Allocation and deallocation through raw pointers: boxes converted to raw
//! pointers with `Box::into_raw`, and freed with `Box::from_raw`.
use core::mem::MaybeUninit;

/// A box allocated uninitialized, initialized through a raw pointer, and freed.
pub fn box_init() -> u32 {
    let p: *mut MaybeUninit<u32> = Box::into_raw(Box::new(MaybeUninit::uninit()));
    unsafe {
        p.cast::<u32>().write(5);
        let b = Box::from_raw(p);
        *b.assume_init()
    }
}

pub fn box_new_uninit() -> u32 {
    let p = Box::into_raw(Box::<u32>::new_uninit());
    unsafe {
        *p.cast::<u32>() = 6;
        *Box::from_raw(p).assume_init()
    }
}

pub fn box_read_write() -> u32 {
    let p = Box::into_raw(Box::new(1u32));
    unsafe {
        *p += 1;
        *Box::from_raw(p)
    }
}

/// Reading a box which has not been initialized is undefined behavior.
pub fn box_read_uninit() -> u32 {
    let p = Box::into_raw(Box::<u32>::new_uninit());
    unsafe { *p.cast::<u32>() }
}

/// Assigning through a raw pointer drops the old value, which must thus be
/// initialized.
pub fn assign_uninit_box() -> u32 {
    let p: *mut MaybeUninit<Box<u32>> = Box::into_raw(Box::new(MaybeUninit::uninit()));
    unsafe {
        let q = p.cast::<Box<u32>>();
        *q = Box::new(1);
        **Box::from_raw(q)
    }
}

/// `ptr::write` does not drop the old value.
pub fn write_uninit_box() -> u32 {
    let p: *mut MaybeUninit<Box<u32>> = Box::into_raw(Box::new(MaybeUninit::uninit()));
    unsafe {
        let q = p.cast::<Box<u32>>();
        q.write(Box::new(1));
        **Box::from_raw(q)
    }
}

/// Freeing twice is undefined behavior.
pub fn double_free() {
    let p = Box::into_raw(Box::new(1u32));
    unsafe {
        let _ = Box::from_raw(p);
        let _ = Box::from_raw(p);
    }
}

/// Using a pointer after freeing it is undefined behavior.
pub fn use_after_free() -> u32 {
    let p = Box::into_raw(Box::new(1u32));
    unsafe {
        let _ = Box::from_raw(p);
        *p
    }
}

/// Freeing a pointer which does not point to the start of a box is undefined
/// behavior.
pub fn free_interior() {
    let p = Box::into_raw(Box::new(1u32));
    unsafe {
        let _ = Box::from_raw(p.add(1));
    }
}

/// Freeing a pointer which does not come from a box is undefined behavior.
pub fn free_borrowed(x: &mut u32) {
    unsafe {
        let _ = Box::from_raw(core::ptr::from_mut(x));
    }
}
