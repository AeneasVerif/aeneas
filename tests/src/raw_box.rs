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

/// Copying a raw pointer creates an alias, not a second allocation owner.
pub fn alias_write(initial: u32, replacement: u32) -> (u32, u32) {
    let p = Box::into_raw(Box::new(initial));
    let alias = p;
    unsafe {
        let before = p.read();
        alias.write(replacement);
        let after = p.read();
        let _owned = Box::from_raw(p);
        (before, after)
    }
}

/// A whole pair occupies one typed cell; updating it preserves its first component.
pub fn replace_pair(first: u32, second: u32, replacement: u32) -> (u32, u32) {
    let p = Box::into_raw(Box::new((first, second)));
    unsafe {
        let old = p.read();
        p.write((old.0, replacement));
        *Box::from_raw(p)
    }
}

/// Pointer addition allows zero and one-past-the-end, but the latter is not read.
pub fn one_past_end(value: u32) -> u32 {
    let p = Box::into_raw(Box::new(value));
    unsafe {
        let start = p.add(0);
        let _end = p.add(1);
        let result = start.read();
        let _owned = Box::from_raw(p);
        result
    }
}

/// A zero-byte Rust value is still one typed cell, not a zero-length model range.
pub fn zero_sized_box() {
    let p = Box::into_raw(Box::new(()));
    unsafe {
        let _value = p.read();
        let _owned = Box::from_raw(p);
    }
}

/// Raw writes are observed when the borrowed Box is used safely again.
pub fn borrowed_box(initial: u32, replacement: u32) -> (u32, u32) {
    let mut b = Box::new(initial);
    let p = core::ptr::from_mut(&mut *b);
    let before = unsafe { p.read() };
    unsafe { p.write(replacement) };
    (before, *b)
}

/// Restoring a borrowed Box also recovers a whole aggregate, including aliases.
pub fn borrowed_pair(first: u32, second: u32, replacement: u32) -> (u32, u32) {
    let mut b = Box::new((first, second));
    let p = core::ptr::from_mut(&mut *b);
    let alias = p;
    let old = unsafe { p.read() };
    unsafe { alias.write((old.0, replacement)) };
    *b
}

#[cfg(test)]
mod tests {
    #[test]
    fn raw_lifecycles() {
        for (initial, replacement) in [(0, 42), (u32::MAX, 0), (7, u32::MAX)] {
            assert_eq!(super::round_trip(initial, replacement), replacement);
            assert_eq!(super::stored_pointer(initial, replacement), replacement);
            assert_eq!(
                super::alias_write(initial, replacement),
                (initial, replacement)
            );
            assert_eq!(
                super::replace_pair(initial, 17, replacement),
                (initial, replacement)
            );
            assert_eq!(super::one_past_end(initial), initial);
            assert_eq!(
                super::borrowed_box(initial, replacement),
                (initial, replacement)
            );
            assert_eq!(
                super::borrowed_pair(initial, 17, replacement),
                (initial, replacement)
            );
        }
        super::zero_sized_box();
    }
}
