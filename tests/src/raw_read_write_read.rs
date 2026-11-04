//@ [!lean] skip

/// # Safety
/// `p` must point to an initialized, writable `u32` for the duration of this call.
pub unsafe fn read_write_read(p: *mut u32) -> (u32, u32) {
    let before = p.read();
    p.write(1);
    (before, p.read())
}

/// # Safety
/// `p` must point to an initialized, writable `u32` for the duration of this call.
pub unsafe fn discarded_read(p: *mut u32) -> u32 {
    let _ = p.read();
    p.write(1);
    p.read()
}

#[cfg(test)]
mod tests {
    #[test]
    fn reads_observe_the_write() {
        let mut value = 0;
        assert_eq!(unsafe { super::read_write_read(&mut value) }, (0, 1));
        assert_eq!(value, 1);
        value = 0;
        assert_eq!(unsafe { super::discarded_read(&mut value) }, 1);
        assert_eq!(value, 1);
    }
}
