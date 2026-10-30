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
