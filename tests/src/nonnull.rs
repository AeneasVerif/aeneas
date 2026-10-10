//@ [!lean] skip
//! `NonNull`, borrows of places behind raw pointers and pointer comparisons, on
//! an intrusive circular doubly linked list: the nodes are boxes which are
//! linked through `NonNull` pointers stored in the nodes.
use core::marker::PhantomData;
use core::ptr::NonNull;

pub struct Node {
    pub value: u32,
    pub next: NonNull<Node>,
    pub prev: NonNull<Node>,
}

pub struct List {
    pub head: Option<NonNull<Node>>,
    pub len: usize,
}

/// Allocate a node which is linked to itself.
pub fn new_node(value: u32) -> NonNull<Node> {
    let p = Box::into_raw(Box::new(Node {
        value,
        next: NonNull::dangling(),
        prev: NonNull::dangling(),
    }));
    let n = unsafe { NonNull::new_unchecked(p) };
    unsafe {
        (*p).next = n;
        (*p).prev = n;
    }
    n
}

/// Free a node allocated with [new_node].
pub fn free_node(n: NonNull<Node>) -> u32 {
    let b = unsafe { Box::from_raw(n.as_ptr()) };
    b.value
}

/// Insert a node which is not in the list at the end of the list.
pub fn push_back(list: &mut List, node: NonNull<Node>) {
    match list.head {
        None => {
            let n = unsafe { &mut *node.as_ptr() };
            n.next = node;
            n.prev = node;
            list.head = Some(node);
        }
        Some(head) => {
            let tail = unsafe { head.as_ref().prev };
            let n = unsafe { &mut *node.as_ptr() };
            n.next = head;
            n.prev = tail;
            unsafe {
                (*tail.as_ptr()).next = node;
                (*head.as_ptr()).prev = node;
            }
        }
    }
    list.len += 1;
}

/// Remove a node which is in the list.
pub fn remove(list: &mut List, node: NonNull<Node>) {
    let n = unsafe { node.as_ref() };
    let next = n.next;
    let prev = n.prev;
    if next == node {
        list.head = None;
    } else {
        unsafe {
            (*prev.as_ptr()).next = next;
            (*next.as_ptr()).prev = prev;
        }
        if list.head == Some(node) {
            list.head = Some(next);
        }
    }
    list.len -= 1;
}

/// Sum the values of the nodes.
pub fn sum(list: &List) -> u32 {
    let mut s = 0u32;
    if let Some(head) = list.head {
        let mut cur = head;
        let mut i = 0;
        while i < list.len {
            let n = unsafe { cur.as_ref() };
            s = s.wrapping_add(n.value);
            cur = n.next;
            i += 1;
        }
    }
    s
}

/// The first node, with the `?` operator on the head pointer.
pub fn front(list: &List) -> Option<&Node> {
    Some(unsafe { list.head?.as_ref() })
}

/// The borrow of the node is dead after the `if`: it is given back to the heap
/// at the end of both branches, before `q` (which may be equal to `p`) is
/// accessed.
pub fn set_values(p: NonNull<Node>, q: NonNull<Node>, b: bool) {
    let n = unsafe { &mut *p.as_ptr() };
    n.value = 1;
    if b {
        n.value = 2;
        unsafe { (*q.as_ptr()).value = 3 };
    }
    unsafe { (*q.as_ptr()).value = 4 };
}

/// A borrow of a field of the node is live across the join: the node is given
/// back to the heap after the join, when the borrow is dead.
pub fn neighbour_value(p: NonNull<Node>, forward: bool) -> u32 {
    let n = unsafe { &mut *p.as_ptr() };
    let r = if forward { &n.next } else { &n.prev };
    let q = *r;
    n.value = n.value.wrapping_add(1);
    unsafe { q.as_ref().value }
}

/// An iterator over the values of the nodes. In `next`, the borrow of the
/// iterator (`&mut self`) is nested inside the borrow of the nodes (`'a`): the
/// backward function of `'a` gives the node back to the heap (it is deferred),
/// the one of the borrow of the iterator is pure.
pub struct Iter<'a> {
    pub cur: Option<NonNull<Node>>,
    pub len: usize,
    pub _marker: PhantomData<&'a Node>,
}

impl<'a> Iter<'a> {
    pub fn next(&mut self) -> Option<&'a u32> {
        if self.len == 0 {
            return None;
        }
        let n = unsafe { self.cur?.as_ref() };
        self.len -= 1;
        self.cur = Some(n.next);
        Some(&n.value)
    }
}

pub fn iter(list: &List) -> Iter<'_> {
    Iter {
        cur: list.head,
        len: list.len,
        _marker: PhantomData,
    }
}

/// The value of the first node, using the iterator.
pub fn first_value(list: &List) -> u32 {
    let mut it = iter(list);
    match it.next() {
        Some(v) => *v,
        None => 0,
    }
}

/// Increment the values of the nodes.
pub fn increment(list: &mut List) {
    if let Some(head) = list.head {
        let mut cur = head;
        let mut i = 0;
        while i < list.len {
            let n = unsafe { cur.as_mut() };
            n.value = n.value.wrapping_add(1);
            cur = n.next;
            i += 1;
        }
    }
}

pub fn test_list() -> u32 {
    let mut list = List { head: None, len: 0 };
    let a = new_node(1);
    let b = new_node(2);
    let c = new_node(3);
    push_back(&mut list, a);
    push_back(&mut list, b);
    push_back(&mut list, c);
    remove(&mut list, b);
    increment(&mut list);
    let s = sum(&list);
    remove(&mut list, a);
    remove(&mut list, c);
    free_node(a);
    free_node(b);
    free_node(c);
    s
}

/// Two mutable borrows of the same node are undefined behavior: the second one
/// fails, because the first one moved the node out of the heap.
pub fn aliasing_borrows(p: NonNull<Node>) {
    let a = unsafe { &mut *p.as_ptr() };
    let b = unsafe { &mut *p.as_ptr() };
    a.value = 1;
    b.value = 2;
}

/// The pointers obtained from borrows point to copies of the borrowed values:
/// comparing them fails.
pub fn compare_views() -> bool {
    let mut x = 0u32;
    let mut y = 0u32;
    NonNull::from(&mut x) == NonNull::from(&mut y)
}

/// `==` on raw pointers (see `RawPtr.eq`).
pub fn same_node(p: *mut Node, q: *const Node) -> bool {
    p as *const Node == q
}

/// Borrows of values in the heap created in the branches of an `if` and used
/// after it: we do not merge them (the code after the `if` is duplicated).
pub fn incr_either(p: NonNull<Node>, q: NonNull<Node>, first: bool) -> u32 {
    let n = if first {
        unsafe { &mut *p.as_ptr() }
    } else {
        unsafe { &mut *q.as_ptr() }
    };
    n.value += 1;
    n.value
}

/// A zero-sized type whose Lean model has two values.
pub struct Empty {
    pub e: core::mem::MaybeUninit<()>,
}

/// Two boxes of a zero-sized type may have the same address: comparing them
/// fails (`RawPtr.eq.fails_zero_sized`).
pub fn compare_zero_sized() -> bool {
    let p = Box::into_raw(Box::new(Empty {
        e: core::mem::MaybeUninit::uninit(),
    }));
    let q = Box::into_raw(Box::new(Empty {
        e: core::mem::MaybeUninit::uninit(),
    }));
    p == q
}
