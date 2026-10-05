//@ [!lean] skip

fn generic_ptr<T>(data: &[T]) -> *const T {
    data.as_ptr()
}
