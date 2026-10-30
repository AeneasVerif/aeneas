use super::*;

mod raw_tests {
    use super::*;

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

mod safe_tests {
    use super::LinkedList;

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
}
