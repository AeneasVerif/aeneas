//@ [!lean] skip
//! Generic code instantiated with function items. A function item is
//! extracted as `A → Result B`, so generic type binders must accept types
//! outside of `Type 0` (`Result` may live in a higher universe).
//!
//! Note: function pointer types (`fn(u8) -> u8`) are not supported by Aeneas;
//! we use function items instead.

fn incr(x: u8) -> u8 {
    x + 1
}

fn apply<F: Fn(u8) -> u8>(f: F, x: u8) -> u8 {
    f(x)
}

fn id<T>(x: T) -> T {
    x
}

pub struct Holder<T> {
    pub x: T,
}

fn get_x<T>(h: Holder<T>) -> T {
    h.x
}

// Methods take `self` by value: borrows of function items are not supported.
pub trait HasOut {
    type Out;
    fn get(self) -> Self::Out;
}

pub struct Wrap<F>(F);

impl<F> HasOut for Wrap<F> {
    type Out = F;
    fn get(self) -> F {
        self.0
    }
}

pub fn use_id(x: u8) -> u8 {
    apply(id(incr), x)
}

pub fn use_some(x: u8) -> Option<u8> {
    match Some(incr) {
        Some(f) => Some(apply(f, x)),
        None => None,
    }
}

pub fn use_holder(x: u8) -> u8 {
    apply(get_x(Holder { x: incr }), x)
}

pub fn use_assoc(x: u8) -> u8 {
    let w = Wrap(incr);
    apply(w.get(), x)
}

pub fn use_option_map(o: Option<u8>) -> Option<u8> {
    o.map(incr)
}

pub fn use_vec(x: u8) -> u8 {
    let v = vec![incr];
    apply(v[0], x)
}
