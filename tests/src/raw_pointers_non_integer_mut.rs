//@ [lean] known-failure
//@ [!lean] skip

fn bool_mut_ptr(data: &mut [bool]) -> *mut bool {
    data.as_mut_ptr()
}
