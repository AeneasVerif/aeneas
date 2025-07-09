//! Adapted from https://en.wikipedia.org/wiki/AVL_tree
#![feature(register_tool)]
#![register_tool(aeneas)]
#![feature(box_patterns)]

impl Ord for i32 {
    fn cmp(&self, other: &Self) -> Ordering {
        if *self < *other {
            Ordering::Less
        } else if *self == *other {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub trait Ord {
    fn cmp(&self, other: &Self) -> Ordering;
}

struct Node<T> {
    value: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
    balance_factor: i8,
}

pub struct Tree<T> {
    root: Option<Box<Node<T>>>,
}

impl<T> Node<T> {
    fn rotate_left(root: &mut Box<Node<T>>, mut z: Box<Node<T>>) {
        // We do (root is X):
        //
        //        X
        //       /
        //      A   Z
        //         / \
        //        B   C
        //
        //        ~>
        //
        //        Z
        //       / \
        //      X   C
        //     / \
        //    A   B

        let b = std::mem::replace(&mut z.left, None);
        root.right = b;
        //        X
        //       / \
        //      A   B
        //
        //        Z
        //         \
        //          C

        let x = std::mem::replace(root, z);
        root.left = Some(x); // root is now Z
                             //        Z
                             //       / \
                             //      X   C
                             //     / \
                             //    A   B

        // Update the balance factors
        if let Some(x) = &mut root.left {
            if root.balance_factor == 0 {
                x.balance_factor = 1;
                root.balance_factor = -1;
            } else {
                x.balance_factor = 0;
                root.balance_factor = 0;
            }
        } else {
            panic!()
        }
    }

    fn rotate_right(root: &mut Box<Node<T>>, mut z: Box<Node<T>>) {
        // We do (root is X):
        //
        //        X
        //         \
        //      Z   C
        //     / \
        //    A   B
        //
        //        ~>
        //
        //        Z
        //       / \
        //      A   X
        //         / \
        //        B   C

        let b = std::mem::replace(&mut z.right, None);
        root.left = b;
        //        X
        //       / \
        //      B   C
        //
        //        Z
        //       /
        //      A

        let x = std::mem::replace(root, z);
        root.right = Some(x); // root is now Z

        // Update the balance factors
        if let Some(x) = &mut root.right {
            if root.balance_factor == 0 {
                x.balance_factor = -1;
                root.balance_factor = 1;
            } else {
                x.balance_factor = 0;
                root.balance_factor = 0;
            }
        } else {
            panic!()
        }
    }

    fn rotate_left_right(root: &mut Box<Node<T>>, mut z: Box<Node<T>>) {
        // We do (root is X):
        //
        //        X
        //         \
        //      Z   1
        //     / \
        //    0   Y
        //       / \
        //      A   B
        //
        //        ~>
        //
        //          Y
        //        /   \
        //      Z       X
        //     / \     / \
        //    0   A   B   1

        let mut y = std::mem::replace(&mut z.right, None).unwrap();
        let a = std::mem::replace(&mut y.left, None);
        let b = std::mem::replace(&mut y.right, None);
        z.right = a;
        root.left = b;

        let x = std::mem::replace(root, y);
        root.left = Some(z);
        root.right = Some(x);

        // Update the balance factors
        if let Some(x) = &mut root.right && let Some(z) = &mut root.left {
            if root.balance_factor == 0 {
                x.balance_factor = 0;
                z.balance_factor = 0;
            }
            else if root.balance_factor < 0 {
                x.balance_factor = 1;
                z.balance_factor = 0;
            }
            else {
                x.balance_factor = 0;
                z.balance_factor = -1;
            }
            root.balance_factor = 0;
        }
        else {
            panic!();
        }
    }

    fn rotate_right_left(root: &mut Box<Node<T>>, mut z: Box<Node<T>>) {
        // We do (root is X):
        //
        //        X
        //       /
        //      1   Z
        //         / \
        //        Y   0
        //       / \
        //      B  A
        //
        //        ~>
        //
        //          Y
        //        /   \
        //      X       Z
        //     / \     / \
        //    1   B   A   0

        let mut y = std::mem::replace(&mut z.left, None).unwrap();
        let b = std::mem::replace(&mut y.left, None);
        let a = std::mem::replace(&mut y.right, None);
        z.left = a;
        root.right = b;

        let x = std::mem::replace(root, y);
        root.left = Some(x);
        root.right = Some(z);

        // Update the balance factors
        if let Some(x) = &mut root.left && let Some(z) = &mut root.right {
            if root.balance_factor == 0 {
                x.balance_factor = 0;
                z.balance_factor = 0;
            }
            else if root.balance_factor > 0 {
                x.balance_factor = -1;
                z.balance_factor = 0;
            }
            else {
                x.balance_factor = 0;
                z.balance_factor = 1;
            }
            root.balance_factor = 0;
        }
        else {
            panic!();
        }
    }
}

impl<T: Ord> Node<T> {
    fn insert_in_left(node: &mut Box<Node<T>>, value: T) -> bool {
        if Tree::insert_in_opt_node(&mut node.left, value) {
            // We increased the height of the left node
            node.balance_factor -= 1;
            if node.balance_factor == -2 {
                // The node is left-heavy: we need to rebalance
                let left = std::mem::replace(&mut node.left, Option::None).unwrap();
                if left.balance_factor <= 0 {
                    // Note that the left balance factor is actually < 0 here
                    Node::rotate_right(node, left);
                } else {
                    Node::rotate_left_right(node, left);
                }
                // In order to udnerstand what happens here we need a drawing.
                // In effect, as we rebalanced the tree, the total height did not
                // increase compared to before the insertion operation.
                false
            } else {
                // If the balance factor changed from 1 to 0: the height did not
                // change (we increased the height of the left subtree, which
                // has now the same height as the right subtree).
                // If it changed from 0 to -1: the subtrees originally had the same
                // height and now the left subtree is strictly heigher than the
                // right subtree: the total height is increased.
                // This means that the height changed iff the new balance factor
                // is different from 0
                node.balance_factor != 0
            }
        } else {
            // The height did not change
            false
        }
    }

    fn insert_in_right(node: &mut Box<Node<T>>, value: T) -> bool {
        // Insert in the right sutbree, and check if we increased its height
        if Tree::insert_in_opt_node(&mut node.right, value) {
            // We increased the height of the right node
            node.balance_factor += 1;

            if node.balance_factor == 2 {
                // The node is right-heavy: we need to rebalance
                let right = std::mem::replace(&mut node.right, Option::None).unwrap();
                if right.balance_factor >= 0 {
                    // Note that the right balance factor is actually > 0 here
                    Node::rotate_left(node, right);
                } else {
                    Node::rotate_right_left(node, right);
                }
                // In order to udnerstand what happens here we need a drawing.
                // In effect, as we rebalanced the tree, the total height did not
                // increase compared to before the insertion operation.
                false
            } else {
                // If the balance factor changed from -1 to 0: the height did not
                // change (we increased the height of the right subtree, which
                // has now the same height as the left subtree).
                // If it changed from 0 to 1: the subtrees originally had the same
                // height and now the right subtree is strictly heigher than the
                // left subtree: the total height is increased.
                // This means that the height changed iff the new balance factor
                // is different from 0
                node.balance_factor != 0
            }
        } else {
            // The height of the right subtree did not change so the total
            // height did not change.
            false
        }
    }

    // Return [true] if we increased the height of the tree
    fn insert(node: &mut Box<Node<T>>, value: T) -> bool {
        let ordering = value.cmp(&(*node).value);

        // Something important: we need to recompute the balance factor
        // from the current balance factor and the change in height. Also,
        // we need to compute whether the height of the current tree increased
        // or not.
        match ordering {
            Ordering::Less => Node::insert_in_left(node, value),
            Ordering::Equal => false,
            Ordering::Greater => Node::insert_in_right(node, value),
        }
    }
}

impl<T: Ord> Tree<T> {
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn find(&self, value: T) -> bool {
        let mut current_tree = &self.root;

        while let Some(current_node) = current_tree {
            match current_node.value.cmp(&value) {
                Ordering::Less => current_tree = &current_node.right,
                Ordering::Equal => return true,
                Ordering::Greater => current_tree = &current_node.left,
            }
        }

        false
    }

    fn insert_in_opt_node(node: &mut Option<Box<Node<T>>>, value: T) -> bool {
        match node {
            Some(node) => Node::insert(node, value),
            None => {
                *node = Some(Box::new(Node {
                    value,
                    left: None,
                    right: None,
                    balance_factor: 0,
                }));
                true
            }
        }
    }

    /// Insert a value and return [true] if the height of the tree increased.
    pub fn insert(&mut self, value: T) -> bool {
        Tree::insert_in_opt_node(&mut self.root, value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Ord for usize {
        fn cmp(&self, other: &Self) -> Ordering {
            if *self < *other {
                Ordering::Less
            } else if *self == *other {
                Ordering::Equal
            } else {
                Ordering::Greater
            }
        }
    }

    fn get_max<T: Ord + Copy>(a: T, b: T) -> T {
        match a.cmp(&b) {
            Ordering::Less => b,
            Ordering::Equal => b,
            Ordering::Greater => a,
        }
    }

    impl<T> Node<T> {
        fn height(&self) -> usize {
            1 + get_max(
                self.right.as_deref().map_or(0, |n| n.height()),
                self.left.as_deref().map_or(0, |n| n.height()),
            )
        }

        fn balance_factor(&self) -> isize {
            self.right.as_deref().map_or(0, |n| n.height()) as isize
                - self.left.as_deref().map_or(0, |n| n.height()) as isize
        }

        fn check_inv(&self) {
            let bf = self.balance_factor();
            assert!(-1 <= bf && bf <= 1);
            assert!(bf == self.balance_factor as isize);
            if let Some(n) = &self.left {
                n.check_inv();
            }
            if let Some(n) = &self.right {
                n.check_inv();
            }
        }
    }

    impl<T> Tree<T> {
        fn check_inv(&self) {
            if let Some(n) = &self.root {
                n.check_inv();
            }
        }
    }

    #[test]
    fn test1() {
        let mut t: Tree<i32> = Tree::new();

        // Always inserting to the right
        for i in 0..100 {
            t.insert(i);
            t.check_inv();
        }
    }

    #[test]
    fn test2() {
        let mut t: Tree<i32> = Tree::new();

        // Always inserting to the left
        for i in 0..(-100) {
            t.insert(i);
            t.check_inv();
        }
    }

    #[test]
    fn test3() {
        let mut t: Tree<i32> = Tree::new();

        // Always inserting to the right
        for i in 0..100 {
            t.insert(i);
            t.check_inv();
        }

        // Always inserting to the left
        for i in 0..(-100) {
            t.insert(i);
            t.check_inv();
        }
    }

    #[test]
    fn test4() {
        let mut t: Tree<i32> = Tree::new();

        // Simulating randomness here
        for i in 0..100 {
            t.insert((i * i + 23 * i) % 17);
            t.check_inv();
        }
    }
}
