//@ [lean] known-failure
//@ [!lean] skip

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
