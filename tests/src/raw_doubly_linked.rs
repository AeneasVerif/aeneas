//@ [!lean] skip
//@ charon-args=--opaque=crate::ext
//@ [lean] subdir=RawDoublyLinked
//@ [lean] aeneas-args=-split-files -all-computable -loops-to-rec

/// Intrusive circular links. Linked nodes must remain at stable addresses.
#[derive(Clone, Copy)]
pub struct Node {
    pub prev: *mut Node,
    pub next: *mut Node,
    pub value: u32,
}

pub mod ext {
    use super::Node;

    /// # Safety
    /// `p` must point to a readable, initialized node with no conflicting borrow.
    pub unsafe fn read_node(p: *mut Node) -> Node {
        p.read()
    }

    /// # Safety
    /// `p` must point to writable node storage with no conflicting borrow.
    pub unsafe fn write_node(p: *mut Node, node: Node) {
        p.write(node);
    }

    pub fn allocate_node(value: u32) -> *mut Node {
        Box::into_raw(Box::new(Node {
            prev: std::ptr::null_mut(),
            next: std::ptr::null_mut(),
            value,
        }))
    }

    /// # Safety
    /// `p` must uniquely own a detached node allocated by `allocate_node`.
    pub unsafe fn take_node(p: *mut Node) -> Node {
        *Box::from_raw(p)
    }
}

/// Initializes detached storage, also the empty-sentinel representation.
///
/// # Safety
/// `node` must point to writable storage for a node, not currently linked.
pub unsafe fn init(node: *mut Node, value: u32) {
    ext::write_node(
        node,
        Node {
            prev: node,
            next: node,
            value,
        },
    );
}

unsafe fn set_next(node: *mut Node, next: *mut Node) {
    let old = ext::read_node(node);
    ext::write_node(node, Node { next, ..old });
}

unsafe fn set_prev(node: *mut Node, prev: *mut Node) {
    let old = ext::read_node(node);
    ext::write_node(node, Node { prev, ..old });
}

/// Inserts a detached node immediately after `left`.
///
/// # Safety
/// `left` belongs to a valid circular doubly-linked ring. `node` is a distinct,
/// initialized detached node. All affected nodes must be writable and remain
/// at stable addresses, without conflicting borrows, throughout their linkage.
pub unsafe fn insert_after(left: *mut Node, node: *mut Node) {
    let before = ext::read_node(left);
    let inserted = ext::read_node(node);
    ext::write_node(
        node,
        Node {
            prev: left,
            next: before.next,
            value: inserted.value,
        },
    );
    set_next(left, node);
    set_prev(before.next, node);
}

/// Unlinks a node and leaves it detached, without freeing its storage.
///
/// # Safety
/// `node` belongs to a valid circular doubly-linked ring. Its neighbours and
/// itself must be writable, live, and free of conflicting borrows. Removing
/// a sentinel from a nonempty ring is not a list operation.
pub unsafe fn remove(node: *mut Node) {
    let old = ext::read_node(node);
    set_next(old.prev, old.next);
    set_prev(old.next, old.prev);
    init(node, old.value);
}

/// Removes and returns the first node of a nonempty sentinel-based list.
///
/// # Safety
/// `root` is the sentinel of a nonempty valid ring, with writable live nodes
/// and no conflicting borrows. The returned node remains allocated.
pub unsafe fn remove_after(root: *mut Node) -> *mut Node {
    let sentinel = ext::read_node(root);
    let node = sentinel.next;
    remove(node);
    node
}

/// An owning list. Only its heap-allocated nodes contain self-referential links,
/// so moving the list does not invalidate pointers.
pub struct LinkedList {
    root: *mut Node,
    len: usize,
}

impl LinkedList {
    pub fn new() -> Self {
        let root = ext::allocate_node(0);
        unsafe { init(root, 0) };
        Self { root, len: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn front(&self) -> Option<u32> {
        if self.is_empty() {
            None
        } else {
            unsafe {
                let sentinel = ext::read_node(self.root);
                Some(ext::read_node(sentinel.next).value)
            }
        }
    }

    pub fn back(&self) -> Option<u32> {
        if self.is_empty() {
            None
        } else {
            unsafe {
                let sentinel = ext::read_node(self.root);
                Some(ext::read_node(sentinel.prev).value)
            }
        }
    }

    pub fn push_front(&mut self, value: u32) {
        let len = self.len.checked_add(1).expect("list length overflow");
        let node = ext::allocate_node(value);
        unsafe {
            init(node, value);
            insert_after(self.root, node);
        }
        self.len = len;
    }

    pub fn pop_front(&mut self) -> Option<u32> {
        if self.is_empty() {
            None
        } else {
            unsafe {
                let node = remove_after(self.root);
                let value = ext::take_node(node).value;
                self.len -= 1;
                Some(value)
            }
        }
    }

    pub fn clear(&mut self) {
        while !self.is_empty() {
            self.pop_front();
        }
    }
}

impl Drop for LinkedList {
    fn drop(&mut self) {
        self.clear();
        unsafe { ext::take_node(self.root) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn safe_interface_matches_plain_sequence() {
        let mut list = LinkedList::new();
        let mut expected = Vec::new();
        let mut seed = 7u32;
        for _ in 0..1000 {
            seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
            if seed & 3 != 0 {
                list.push_front(seed);
                expected.push(seed);
            } else {
                assert_eq!(list.pop_front(), expected.pop());
            }
            assert_eq!(list.len(), expected.len());
            assert_eq!(list.is_empty(), expected.is_empty());
            assert_eq!(list.front(), expected.last().copied());
            assert_eq!(list.back(), expected.first().copied());
        }
        let mut moved = list;
        while let Some(value) = expected.pop() {
            assert_eq!(moved.pop_front(), Some(value));
        }
        assert_eq!(moved.pop_front(), None);
        moved.push_front(42);
        moved.clear();
        moved.clear();
        assert_eq!(moved.front(), None);
        assert_eq!(moved.back(), None);
        moved.push_front(99);
        assert_eq!(moved.pop_front(), Some(99));
        moved.push_front(100);
    }

    fn blank(value: u32) -> Node {
        Node {
            prev: std::ptr::null_mut(),
            next: std::ptr::null_mut(),
            value,
        }
    }

    unsafe fn assert_ring(root: *mut Node, expected: &[(*mut Node, u32)]) {
        let sentinel = ext::read_node(root);
        let mut previous = root;
        let mut cursor = sentinel.next;
        for &(pointer, value) in expected {
            assert_eq!(cursor, pointer);
            let node = ext::read_node(cursor);
            assert_eq!(node.prev, previous);
            assert_eq!(node.value, value);
            previous = cursor;
            cursor = node.next;
        }
        assert_eq!(cursor, root);
        assert_eq!(sentinel.prev, previous);
        let mut next = root;
        cursor = sentinel.prev;
        for &(pointer, value) in expected.iter().rev() {
            assert_eq!(cursor, pointer);
            let node = ext::read_node(cursor);
            assert_eq!(node.next, next);
            assert_eq!(node.value, value);
            next = cursor;
            cursor = node.prev;
        }
        assert_eq!(cursor, root);
        assert_eq!(sentinel.next, next);
    }

    unsafe fn assert_detached(node: *mut Node, value: u32) {
        let actual = ext::read_node(node);
        assert_eq!(actual.prev, node);
        assert_eq!(actual.next, node);
        assert_eq!(actual.value, value);
    }

    #[test]
    fn empty_singleton_and_middle_updates() {
        let mut storage = [blank(0), blank(1), blank(2), blank(3), blank(99)];
        unsafe {
            let root = storage.as_mut_ptr();
            let a = root.add(1);
            let b = root.add(2);
            let c = root.add(3);
            for i in 0..5 {
                init(root.add(i), storage[i].value);
            }
            assert_ring(root, &[]);
            insert_after(root, a);
            assert_ring(root, &[(a, 1)]);
            insert_after(a, c);
            insert_after(a, b);
            assert_ring(root, &[(a, 1), (b, 2), (c, 3)]);
            remove(b);
            assert_detached(b, 2);
            assert_ring(root, &[(a, 1), (c, 3)]);
            assert_eq!(remove_after(root), a);
            assert_detached(a, 1);
            assert_ring(root, &[(c, 3)]);
            remove(c);
            assert_detached(c, 3);
            assert_ring(root, &[]);
            assert_detached(root.add(4), 99);
        }
    }

    #[test]
    fn insertion_and_removal_orders() {
        let permutations = [
            [1usize, 2, 3],
            [1, 3, 2],
            [2, 1, 3],
            [2, 3, 1],
            [3, 1, 2],
            [3, 2, 1],
        ];
        for insertion in permutations {
            for removal in permutations {
                let mut storage = [blank(0), blank(1), blank(2), blank(3)];
                unsafe {
                    let root = storage.as_mut_ptr();
                    for i in 0..4 {
                        init(root.add(i), i as u32);
                    }
                    let mut expected = Vec::new();
                    for i in insertion {
                        insert_after(root, root.add(i));
                        expected.insert(0, (root.add(i), i as u32));
                        assert_ring(root, &expected);
                    }
                    for i in removal {
                        remove(root.add(i));
                        expected.retain(|&(pointer, _)| pointer != root.add(i));
                        assert_ring(root, &expected);
                        assert_detached(root.add(i), i as u32);
                    }
                }
            }
        }
    }

    #[test]
    fn removing_detached_node_is_idempotent() {
        let mut storage = blank(7);
        unsafe {
            let node = std::ptr::from_mut(&mut storage);
            init(node, 7);
            remove(node);
            remove(node);
            assert_detached(node, 7);
        }
    }
}
