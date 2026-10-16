//@ [!lean] skip
//! Implementations of a trait for a type which contains raw pointers (an
//! intrusive node). A function accesses the heap only if it dereferences raw
//! pointers (or calls a function which does): `Node::links` and
//! `Node::links_mut` only borrow a field holding `NonNull`s, so they are pure,
//! and their signatures match the (pure) signatures of the trait methods.
use core::ptr::NonNull;

pub struct Links<T> {
    pub next: NonNull<T>,
    pub prev: NonNull<T>,
}

pub trait Linkable: Sized {
    fn links(&self) -> &Links<Self>;
    fn links_mut(&mut self) -> &mut Links<Self>;
}

pub struct Node {
    pub value: u32,
    links: Links<Node>,
}

impl Linkable for Node {
    fn links(&self) -> &Links<Node> {
        &self.links
    }

    fn links_mut(&mut self) -> &mut Links<Node> {
        &mut self.links
    }
}

/// Pure: it manipulates raw pointers as values only.
pub fn swap_links<T>(l: &mut Links<T>) {
    let n = l.next;
    l.next = l.prev;
    l.prev = n;
}

/// Pure: it moves raw pointers into a structure.
pub fn mk_links<T>(next: NonNull<T>, prev: NonNull<T>) -> Links<T> {
    Links { next, prev }
}

/// Accesses the heap (through `as_ref`), and calls the trait method.
pub unsafe fn next<T: Linkable>(p: NonNull<T>) -> NonNull<T> {
    unsafe { p.as_ref().links().next }
}

/// Accesses the heap (by dereferencing a raw pointer), and calls the trait
/// method.
pub unsafe fn link_self<T: Linkable>(p: NonNull<T>) {
    let l = unsafe { (*p.as_ptr()).links_mut() };
    l.next = p;
    l.prev = p;
}

pub fn new_node(value: u32) -> NonNull<Node> {
    let p = Box::into_raw(Box::new(Node {
        value,
        links: Links {
            next: NonNull::dangling(),
            prev: NonNull::dangling(),
        },
    }));
    let n = unsafe { NonNull::new_unchecked(p) };
    unsafe { link_self(n) };
    n
}

/// A self-linked node is its own successor.
pub fn self_next(value: u32) -> bool {
    let n = new_node(value);
    unsafe { next(n) == n }
}
