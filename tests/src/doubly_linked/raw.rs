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
