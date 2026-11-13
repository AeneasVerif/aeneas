//@ [!borrow-check] skip
//@ [borrow-check] known-failure
//@ [borrow-check] aeneas-args=-log-error MainLogger
//! Negative borrow-check tests for `#[verify::stateful_lifetime]` soundness checks.
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::opaque]
pub struct Ptr<T> {
    data: *mut T,
}

impl<T> Copy for Ptr<T> {}
impl<T> Clone for Ptr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Ptr<T> {
    #[verify::stateful_lifetime(short)]
    #[verify::opaque]
    pub fn as_mut<'a>(self) -> &'a mut T {
        unsafe { &mut *(self.data) }
    }

    #[verify::stateful_lifetime(long)]
    #[verify::opaque]
    pub fn from_mut<'a>(r: &'a mut T) -> Ptr<T> {
        Self { data: &raw mut *r }
    }

    #[verify::stateful_lifetime(long)]
    #[verify::opaque]
    pub fn from_shr<'a>(r: &'a T) -> Self {
        Self {
            data: (&raw const *r) as *mut _,
        }
    }
}

static STATIC_VAL: i32 = 0;

// 1. Outliving stateful lifetimes (`'a: 'b`) where ending `'a` must end parent `'b`
//    and would duplicate `'b`'s stateful backward call.
#[verify::stateful_lifetime]
pub fn dependent_stateful_lifetimes<'a: 'b, 'b>(
    x: &'a mut i32,
    y: &'b mut i32,
) -> (&'a mut i32, &'b mut i32) {
    let px = Ptr::from_mut(x);
    let py = Ptr::from_mut(y);
    (px.as_mut(), py.as_mut())
}

// 2. Unattached `'static` stateful abstraction with multiple stateful lifetimes:
//    ambiguous which backward function should run `from_shr_back`.
#[verify::stateful_lifetime]
pub fn unattached_with_two_stateful_lifetimes<'a, 'b>(
    x: &'a mut i32,
    y: &'b mut i32,
) -> (&'a mut i32, &'b mut i32) {
    let _st = Ptr::from_shr(&STATIC_VAL);
    (x, y)
}

// 3. Returning an active stateful borrow from a function not marked
//    `#[verify::stateful_lifetime]`.
pub fn missing_stateful_lifetime_attr<'a>(p: Ptr<i32>, _w: &'a i32) -> &'a mut i32 {
    p.as_mut()
}

// 4. Marking only `'a` as `#[verify::stateful_lifetime]` while `'b`'s pure
//    backward function needs to end an active stateful borrow.
#[verify::stateful_lifetime('a)]
pub fn non_stateful_rg_ending_stateful_abs<'a, 'b>(
    x: &'a mut i32,
    y: &'b mut i32,
) -> (&'a mut i32, &'b mut i32) {
    let py = Ptr::from_mut(y);
    (x, py.as_mut())
}

pub fn id_mut<'a, T>(x: &'a mut T) -> &'a mut T {
    x
}

// 5. Outliving stateful lifetimes (`'a: 'b`) where `'b` only has a pure borrow
//    (`id_mut(y)`), which would still force `'a`'s backward function to end `'b`.
#[verify::stateful_lifetime]
pub fn outlives_with_pure_borrow_in_b<'a: 'b, 'b>(
    x: &'a mut i32,
    y: &'b mut i32,
) -> (&'a mut i32, &'b mut i32) {
    let px = Ptr::from_mut(x);
    (px.as_mut(), id_mut(y))
}

// 6. Marking only `'a` as `#[verify::stateful_lifetime]` while returning a
//    stateful output borrow (`as_mut`) in an independent non-stateful lifetime `'b`.
#[verify::stateful_lifetime('a)]
pub fn output_stateful_borrow_in_non_stateful_lifetime<'a, 'b>(
    x: &'a mut i32,
    _w: &'b i32,
) -> &'b mut i32 {
    let px = Ptr::from_mut(x);
    px.as_mut()
}

// 7. Same with `'a: 'b` outlives clause (`coerce_only_a`).
#[verify::stateful_lifetime('a)]
pub fn coerce_only_a<'a: 'b, 'b>(x: &'a mut i32) -> &'b mut i32 {
    let px = Ptr::from_mut(x);
    px.as_mut()
}
