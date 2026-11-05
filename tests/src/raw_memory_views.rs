//@ [!lean] skip
//@ [lean] aeneas-args=-loops-to-rec
//@ [lean] known-failure

//! Companion to raw_scale.rs: cases needing more than a typed, initialized heap.
//! These are public entry points, unlike the older cfg(test)-only scenarios.
//! Native behavior and extraction status are separate; see tests/lean/EXTRACTION.md.

/// A first write needs writable bytes, not a readable old u32.
pub fn first_heap_write(value: u32) -> u32 {
    let layout = std::alloc::Layout::new::<u32>();
    unsafe {
        let allocation = std::alloc::alloc(layout);
        if allocation.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        let word = allocation.cast::<u32>();
        word.write(value);
        let result = word.read();
        std::alloc::dealloc(allocation, layout);
        result
    }
}

/// One storage region, two typed views; native endianness is explicit.
/// Only words 0 and 7 change. No padding or invalid u16 representations exist.
pub fn update_word_bytes(words: &mut [u16; 8], first: u16, last: u16) {
    let first = first.to_ne_bytes();
    let last = last.to_ne_bytes();
    let bytes = unsafe { std::slice::from_raw_parts_mut(words.as_mut_ptr().cast::<u8>(), 16) };
    bytes[0] = first[0];
    bytes[1] = first[1];
    bytes[14] = last[0];
    bytes[15] = last[1];
}

/// Observe a stored pointer's numerical address without destroying its provenance.
/// This deliberately does NOT reconstruct a pointer from the resulting integer.
///
/// # Safety
/// `slot` must permit an aligned pointer-sized read of an initialized thin pointer
/// whose address bytes are initialized (for example one obtained from a live u32).
/// The target ABI must give usize the pointer's size and compatible alignment.
pub unsafe fn stored_pointer_address(slot: *const *mut u32) -> usize {
    unsafe { slot.cast::<usize>().read() }
}

/// Copy pointer bytes, preserving the address and provenance even for a dangling pointer.
///
/// # Safety
/// `source` must point to an initialized thin pointer; `destination` must permit
/// writing one pointer. Their storage must be disjoint and pointer-aligned.
/// The pointee need not be live; this function does not dereference it.
pub unsafe fn copy_stored_pointer(source: *const *mut u32, destination: *mut *mut u32) -> *mut u32 {
    unsafe {
        std::ptr::copy(
            source.cast::<u8>(),
            destination.cast::<u8>(),
            std::mem::size_of::<*mut u32>(),
        );
        destination.read()
    }
}

/// Numerical equality is not evidence of equal provenance or access permission.
pub fn same_address(p: *const u32, q: *const u32) -> bool {
    p.addr() == q.addr()
}

/// The saved pointer can still be copied and observed after physical deallocation.
/// No access is made to the dead allocation.
pub fn copy_after_deallocation(value: u32) -> (usize, usize) {
    let layout = std::alloc::Layout::new::<u32>();
    unsafe {
        let allocation = std::alloc::alloc(layout);
        if allocation.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        let word = allocation.cast::<u32>();
        word.write(value);
        let saved = word;
        let before = saved.addr();
        std::alloc::dealloc(allocation, layout);
        let mut copied = std::mem::MaybeUninit::<*mut u32>::uninit();
        let pointer = copy_stored_pointer(&saved, copied.as_mut_ptr());
        (before, pointer.addr())
    }
}

fn fill_safe(bytes: &mut [u8], value: u8) {
    let mut i = 0;
    while i < bytes.len() {
        bytes[i] = value;
        i += 1;
    }
}

unsafe fn fill_raw(bytes: *mut u8, length: usize, value: u8) {
    let mut i = 0;
    while i < length {
        unsafe { bytes.add(i).write(value) };
        i += 1;
    }
}

fn update_middle(middle: &mut [u8]) {
    fill_safe(middle, 2);
    {
        let smaller = &mut middle[3..7];
        unsafe { fill_raw(smaller.as_mut_ptr(), smaller.len(), 3) };
    }
    fill_safe(&mut middle[10..], 4);
}

/// Box -> raw -> safe subslice -> smaller raw exposure -> safe -> raw -> Box.
/// Framing preserves the first/last two bytes; only the original Box is reclaimed.
/// Unlike raw_scale's pure safe helper, this needs nested return authority.
pub fn nested_views() -> Box<[u8; 16]> {
    let outer = Box::into_raw(Box::new([1u8; 16]));
    unsafe {
        {
            let middle = std::slice::from_raw_parts_mut(outer.cast::<u8>().add(2), 12);
            update_middle(middle);
        }
        Box::from_raw(outer)
    }
}

/// Disjoint siblings, a shared child, an empty child, and a separate mutation.
pub fn composed_views(bytes: &mut [u8; 4], unrelated: &mut u8) {
    let (left, right) = bytes.split_at_mut(2);
    unsafe {
        let l = left.as_mut_ptr();
        let r = right.as_mut_ptr();
        {
            let shared = std::slice::from_raw_parts(l, 2);
            assert_eq!(shared.len(), 2);
            let empty = std::slice::from_raw_parts(r, 0);
            assert!(empty.is_empty());
        }
        l.write(10);
        r.add(1).write(20);
        *unrelated = 99;
    }
}

#[repr(C, align(2))]
struct Padded {
    tag: u8,
}

/// Initialize fields without reading padding; copying preserves raw storage.
pub fn padded_copy(tag: u8) -> u8 {
    let mut source = std::mem::MaybeUninit::<Padded>::uninit();
    let mut destination = std::mem::MaybeUninit::<Padded>::uninit();
    unsafe {
        std::ptr::addr_of_mut!((*source.as_mut_ptr()).tag).write(tag);
        std::ptr::copy_nonoverlapping(source.as_ptr(), destination.as_mut_ptr(), 1);
        let result = destination.assume_init();
        result.tag
    }
}

struct ObservedBox<'a> {
    pointer: *mut u8,
    events: &'a mut Vec<u8>,
}

impl Drop for ObservedBox<'_> {
    fn drop(&mut self) {
        unsafe {
            let value = self.pointer.read();
            drop(Box::from_raw(self.pointer));
            self.events.push(value);
        }
    }
}

/// A non-Copy owner is moved once and dropped once on this terminating path.
/// Forgetting the owner or aborting is deliberately not a cleanup guarantee.
pub fn drop_owned_byte(value: u8) -> Vec<u8> {
    let mut events = Vec::with_capacity(1);
    let owner = ObservedBox {
        pointer: Box::into_raw(Box::new(value)),
        events: &mut events,
    };
    let moved = owner;
    drop(moved);
    events
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initialization_and_reinterpreted_words() {
        for value in [0, 1, 0x1234_5678, u32::MAX] {
            assert_eq!(first_heap_write(value), value);
        }
        let mut words = [1, 2, 3, 4, 5, 6, 7, 8];
        update_word_bytes(&mut words, 0x4321, 0x8765);
        assert_eq!(words, [0x4321, 2, 3, 4, 5, 6, 7, 0x8765]);
    }

    #[test]
    fn numerical_observation_preserves_stored_pointer() {
        let mut target = 37u32;
        let pointer = &mut target as *mut u32;
        let slot = pointer;
        unsafe {
            assert_eq!(stored_pointer_address(&slot), pointer.addr());
            slot.write(41);
            assert_eq!(slot.read(), 41);
        }
        assert_eq!(target, 41);
    }

    #[test]
    fn copied_pointer_retains_access_and_survives_pointee_deallocation() {
        let mut target = 37u32;
        let saved = &mut target as *mut u32;
        let mut destination = std::mem::MaybeUninit::<*mut u32>::uninit();
        unsafe {
            let copied = copy_stored_pointer(&saved, destination.as_mut_ptr());
            assert!(same_address(saved, copied));
            copied.write(41);
        }
        assert_eq!(target, 41);
        for value in [0, u32::MAX] {
            let (before, after) = copy_after_deallocation(value);
            assert_eq!(before, after);
        }
    }

    #[test]
    fn nested_exposures_preserve_the_frame_and_ownership() {
        let mut result = nested_views();
        assert_eq!(*result, [1, 1, 2, 2, 2, 3, 3, 3, 3, 2, 2, 2, 4, 4, 1, 1]);
        result[15] = 5;
        assert_eq!(result[15], 5);
    }

    #[test]
    fn composed_siblings_and_destructor() {
        let mut bytes = [1, 2, 3, 4];
        let mut unrelated = 5;
        composed_views(&mut bytes, &mut unrelated);
        assert_eq!(bytes, [10, 2, 3, 20]);
        assert_eq!(unrelated, 99);
        for value in [0, 37, u8::MAX] {
            assert_eq!(drop_owned_byte(value), vec![value]);
            assert_eq!(padded_copy(value), value);
        }
    }

    #[test]
    fn valid_restricted_values_and_zero_sized_access() {
        for byte in [0u8, 1] {
            let value = unsafe { (std::ptr::addr_of!(byte).cast::<bool>()).read() };
            assert_eq!(value, byte == 1);
        }
        let mut units = [(); 4];
        unsafe {
            let p = units.as_mut_ptr();
            assert_eq!(p.read(), ());
            assert_eq!(std::slice::from_raw_parts(p, 0).len(), 0);
            p.write(());
        }
    }

    #[test]
    fn mutable_pointer_byte_views() {
        let mut target = 37u8;
        let mut pointer = &mut target as *mut u8;
        let before = pointer.addr();
        unsafe {
            let byte = &mut *std::ptr::addr_of_mut!(pointer).cast::<u8>();
            std::hint::black_box(*byte);
            // No write: the original pointer is still usable.
            assert_eq!(pointer.read(), 37);
            let byte = &mut *std::ptr::addr_of_mut!(pointer).cast::<u8>();
            let saved = *byte;
            *byte = saved;
        }
        // Same numerical value is not a justification for dereferencing it.
        assert_eq!(pointer.addr(), before);
    }
}
