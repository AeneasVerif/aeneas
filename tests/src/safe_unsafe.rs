//@ [!lean] skip
//@ [lean] subdir=SafeUnsafe
//! Adequacy of the raw-pointer model: small programs mixing safe code with
//! `unsafe` raw-pointer primitives (`ptr::from_mut`, `as_ptr`/`as_mut_ptr`,
//! `slice::from_raw_parts(_mut)`, `Box::into_raw`/`from_raw`, `ptr::read`,
//! `as_mut`, `NonNull`).
//!
//! Every function is closed (`non_null_write` aside), so that its behaviour is
//! fixed. Each one documents what Miri reports, with Stacked Borrows (the
//! default) and Tree Borrows alike: `ok(n)` (no UB, returns `n`) or `UB`. The
//! Lean proofs in `tests/lean/SafeUnsafe/Proofs.lean` relate the extracted model
//! to the verdict, and sum up the cases where the model is stricter than Rust
//! (incomplete) or misses UB or the result (unsound).
//!
//! Reproduce the verdicts with a crate containing this file as a module
//! (`#[path = ".../safe_unsafe.rs"] mod safe_unsafe;`):
//! `cargo +nightly miri test -- --exact safe_unsafe::miri::<name>`, with
//! `MIRIFLAGS=-Zmiri-tree-borrows` for Tree Borrows. Leaked memory makes Miri
//! report an error at exit; `-Zmiri-ignore-leaks` silences it.
use core::ptr;
use core::slice;

// ---------------------------------------------------------------------------
// `ptr::from_mut`: a raw pointer to a local
// ---------------------------------------------------------------------------

/// The write through the pointer is visible through the local. ok(5)
pub fn from_mut_write_then_read() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    unsafe { *p = 5 };
    x
}

/// Writing the local invalidates the pointer: the write through it is UB. UB
pub fn from_mut_write_after_owner_write() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    x = 2;
    unsafe { *p = 5 };
    x
}

/// Reading the local does not invalidate the pointer. ok(10)
pub fn from_mut_read_after_owner_read() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    unsafe { *p = 5 };
    let y = x;
    let z = unsafe { *p };
    y + z
}

/// A second `&mut x` invalidates the first pointer. UB
pub fn from_mut_twice() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    let q = ptr::from_mut(&mut x);
    unsafe {
        *q = 2;
        *p = 3;
    }
    x
}

fn ptr_to_local() -> *mut u32 {
    let mut x = 1u32;
    ptr::from_mut(&mut x)
}

/// The local is dead once `ptr_to_local` returns. UB
pub fn from_mut_dangling() -> u32 {
    let p = ptr_to_local();
    unsafe { *p }
}

fn escape(x: &mut u32) -> *mut u32 {
    ptr::from_mut(x)
}

/// The pointer outlives the call to `escape`, and stays valid as long as `x`
/// is not used. ok(7)
pub fn from_mut_escape() -> u32 {
    let mut x = 1u32;
    let p = escape(&mut x);
    unsafe { *p = 7 };
    x
}

unsafe fn write_through(p: *mut u32, v: u32) {
    *p = v;
}

/// The write happens in an `unsafe` callee. ok(8)
pub fn from_mut_write_in_callee() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    unsafe { write_through(p, 8) };
    x
}

// ---------------------------------------------------------------------------
// `as_ptr`/`as_mut_ptr`: raw pointers into an array
// ---------------------------------------------------------------------------

/// The writes through the pointer are visible in the array. ok(7)
pub fn as_mut_ptr_write() -> u32 {
    let mut a = [0u32; 4];
    let p = a.as_mut_ptr();
    unsafe { *p.add(3) = 7 };
    a[3]
}

/// `add` may compute the pointer one past the end... ok(0)
pub fn as_mut_ptr_one_past_end() -> u32 {
    let mut a = [0u32; 4];
    let p = a.as_mut_ptr();
    let _q = unsafe { p.add(4) };
    a[0]
}

/// ... but not write through it. UB
pub fn as_mut_ptr_write_one_past_end() -> u32 {
    let mut a = [0u32; 4];
    let p = a.as_mut_ptr();
    unsafe { *p.add(4) = 7 };
    a[0]
}

/// `add` may not go further than one past the end. UB
pub fn as_mut_ptr_add_out_of_bounds() -> u32 {
    let mut a = [0u32; 4];
    let p = a.as_mut_ptr();
    let _q = unsafe { p.add(5) };
    a[0]
}

/// Writing the array invalidates the shared pointer. UB
pub fn as_ptr_read_after_owner_write() -> u32 {
    let mut a = [1u32, 2];
    let p = a.as_ptr();
    a[0] = 5;
    unsafe { *p }
}

/// Reading through the slice and through the pointer, both shared. ok(3)
pub fn as_ptr_read_while_shared() -> u32 {
    let a = [1u32, 2];
    let s: &[u32] = &a;
    let p = s.as_ptr();
    let x = s[1];
    x + unsafe { *p }
}

/// The two pointers of the two calls are the same, but the second call
/// reborrows the array mutably, which invalidates the first pointer. UB
pub fn as_mut_ptr_twice() -> u32 {
    let mut a = [0u32; 2];
    let p = a.as_mut_ptr();
    let q = a.as_mut_ptr();
    unsafe {
        *q = 1;
        *p = 2;
    }
    a[0]
}

// ---------------------------------------------------------------------------
// `Box::into_raw`/`Box::from_raw`
// ---------------------------------------------------------------------------

/// ok(4)
pub fn box_roundtrip() -> u32 {
    let p = Box::into_raw(Box::new(3u32));
    unsafe {
        *p = 4;
        *Box::from_raw(p)
    }
}

/// The second `from_raw` frees the memory again. UB
pub fn box_double_free() -> u32 {
    let p = Box::into_raw(Box::new(3u32));
    unsafe {
        let x = *Box::from_raw(p);
        let y = *Box::from_raw(p);
        x + y
    }
}

/// UB
pub fn box_use_after_free() -> u32 {
    let p = Box::into_raw(Box::new(3u32));
    unsafe {
        let x = *Box::from_raw(p);
        x + *p
    }
}

/// Freeing a local through `Box::from_raw`. UB
pub fn box_free_local() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    unsafe { *Box::from_raw(p) }
}

/// Freeing an array element through `Box::from_raw`. UB
pub fn box_free_array_element() -> u32 {
    let mut a = [1u32, 2];
    let p = a.as_mut_ptr();
    unsafe { *Box::from_raw(p) }
}

/// Leaking memory is not UB (Miri reports the leak at exit). ok(3)
pub fn box_leak() -> u32 {
    let p = Box::into_raw(Box::new(3u32));
    unsafe { *p }
}

// ---------------------------------------------------------------------------
// `slice::from_raw_parts(_mut)`: borrows from raw pointers
// ---------------------------------------------------------------------------

/// ok(9)
pub fn from_raw_parts_mut_write() -> u32 {
    let p = Box::into_raw(Box::new(1u32));
    let s = unsafe { slice::from_raw_parts_mut(p, 1) };
    s[0] = 9;
    unsafe { *Box::from_raw(p) }
}

/// The slice is longer than the allocation. UB
pub fn from_raw_parts_too_long() -> u32 {
    let p = Box::into_raw(Box::new(1u32));
    let s = unsafe { slice::from_raw_parts(p as *const u32, 2) };
    let x = s[0];
    x + unsafe { *Box::from_raw(p) }
}

/// Writing through the pointer while the shared slice is live. UB
pub fn from_raw_parts_write_while_shared() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    let s = unsafe { slice::from_raw_parts(p as *const u32, 1) };
    unsafe { *p = 2 };
    s[0]
}

/// Reading through the pointer while the shared slice is live. ok(2)
pub fn from_raw_parts_read_while_shared() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    let s = unsafe { slice::from_raw_parts(p as *const u32, 1) };
    let y = unsafe { *p };
    s[0] + y
}

/// A slice over the raw-pointer view of an array: the write through the slice
/// is visible in the array. ok(5)
pub fn from_raw_parts_mut_over_array() -> u32 {
    let mut a = [0u32; 2];
    let p = a.as_mut_ptr();
    let s = unsafe { slice::from_raw_parts_mut(p, 2) };
    s[1] = 5;
    a[1]
}

// ---------------------------------------------------------------------------
// `ptr::read` copies the bytes: for a non-`Copy` type, the copy and the
// original both own the value
// ---------------------------------------------------------------------------

/// Two owners of the `Box`. UB (TB: double free; SB: reading `*b` invalidates `b2` first)
pub fn ptr_read_box_double_free() -> u32 {
    let mut b = Box::new(1u32);
    let p = ptr::from_mut(&mut b);
    let b2 = unsafe { ptr::read(p) };
    *b2 + *b
}

/// `ptr::read` on a `Copy` type. ok(2)
pub fn ptr_read_copy() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    let y = unsafe { ptr::read(p) };
    x + y
}

// ---------------------------------------------------------------------------
// `as_mut`: a `&mut` from a raw pointer (no Lean model: extracted as an axiom)
// ---------------------------------------------------------------------------

/// ok(6)
pub fn ptr_as_mut_write() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    if let Some(r) = unsafe { p.as_mut() } {
        *r = 6;
    }
    x
}

/// Two live `&mut` to the same place. UB
/// (`if let` rather than `unwrap`: the extracted call to `unwrap` on an
/// `Option<&mut T>` has a backward function, which the Lean model of `unwrap`
/// lacks, so the extracted code does not type-check.)
pub fn ptr_as_mut_twice() -> u32 {
    let mut x = 1u32;
    let p = ptr::from_mut(&mut x);
    if let Some(r1) = unsafe { p.as_mut() } {
        if let Some(r2) = unsafe { p.as_mut() } {
            *r2 = 2;
            *r1 = 3;
        }
    }
    x
}

// ---------------------------------------------------------------------------
// `NonNull::from(&mut x)`: an opaque type hides the raw pointer
// ---------------------------------------------------------------------------

/// ok(v)
pub fn non_null_write(v: u32) -> u32 {
    let mut x = 1u32;
    let p = ptr::NonNull::from(&mut x);
    unsafe { *p.as_ptr() = v };
    x
}

#[cfg(miri)]
mod miri {
    macro_rules! verdicts {
        ($($name:ident),*) => {
            $(#[test] fn $name() { std::println!("{}", super::$name()); })*
        };
    }
    verdicts!(
        from_mut_write_then_read,
        from_mut_write_after_owner_write,
        from_mut_read_after_owner_read,
        from_mut_twice,
        from_mut_dangling,
        from_mut_escape,
        from_mut_write_in_callee,
        as_mut_ptr_write,
        as_mut_ptr_one_past_end,
        as_mut_ptr_write_one_past_end,
        as_mut_ptr_add_out_of_bounds,
        as_ptr_read_after_owner_write,
        as_ptr_read_while_shared,
        as_mut_ptr_twice,
        box_roundtrip,
        box_double_free,
        box_use_after_free,
        box_free_local,
        box_free_array_element,
        box_leak,
        from_raw_parts_mut_write,
        from_raw_parts_too_long,
        from_raw_parts_write_while_shared,
        from_raw_parts_read_while_shared,
        from_raw_parts_mut_over_array,
        ptr_read_box_double_free,
        ptr_read_copy,
        ptr_as_mut_write,
        ptr_as_mut_twice
    );
    #[test]
    fn non_null_write() {
        std::println!("{}", super::non_null_write(4));
    }
}
