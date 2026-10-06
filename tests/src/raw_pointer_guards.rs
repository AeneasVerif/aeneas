//@ [!lean] skip
//! Drop guards manipulating raw pointers (from pin-project-lite).
use core::mem::ManuallyDrop;
use core::ptr;

pub struct UnsafeDropInPlaceGuard<T: ?Sized>(*mut T);

impl<T: ?Sized> Drop for UnsafeDropInPlaceGuard<T> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.0);
        }
    }
}

pub struct UnsafeOverwriteGuard<T> {
    target: *mut T,
    value: ManuallyDrop<T>,
}

impl<T> UnsafeOverwriteGuard<T> {
    pub unsafe fn new(target: *mut T, value: T) -> Self {
        Self {
            target,
            value: ManuallyDrop::new(value),
        }
    }
}

impl<T> Drop for UnsafeOverwriteGuard<T> {
    /// The raw pointer to `*self.value` is not used anymore when the function
    /// returns: we free its memory in the forward function.
    fn drop(&mut self) {
        unsafe {
            ptr::write(self.target, ptr::read(&*self.value));
        }
    }
}
