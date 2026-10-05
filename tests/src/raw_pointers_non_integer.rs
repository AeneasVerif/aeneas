//@ [lean] known-failure
//@ [!lean] skip

fn bool_ptr(data: &[bool]) -> *const bool {
    data.as_ptr()
}
