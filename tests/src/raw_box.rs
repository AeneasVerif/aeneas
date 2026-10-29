//@ [!lean] skip

pub fn round_trip(initial: u32, replacement: u32) -> u32 {
    let p = Box::into_raw(Box::new(initial));
    unsafe {
        p.write(replacement);
        let value = p.read();
        let _owned = Box::from_raw(p);
        value
    }
}

pub fn stored_pointer(initial: u32, replacement: u32) -> u32 {
    let target = Box::into_raw(Box::new(initial));
    let slot = Box::into_raw(Box::new(target));
    unsafe {
        let loaded = slot.read();
        loaded.write(replacement);
        let _slot = Box::from_raw(slot);
        *Box::from_raw(target)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn raw_lifecycles() {
        for (initial, replacement) in [(0, 42), (u32::MAX, 0), (7, u32::MAX)] {
            assert_eq!(super::round_trip(initial, replacement), replacement);
            assert_eq!(super::stored_pointer(initial, replacement), replacement);
        }
    }
}
