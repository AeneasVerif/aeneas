//@ [!lean] skip

fn generic_mut_ptr<T>(data: &mut [T]) -> *mut T {
    data.as_mut_ptr()
}
