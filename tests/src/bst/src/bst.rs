//! Adapted from https://github.com/RaitoBezarius/avl-verification
#![feature(register_tool)]
#![register_tool(aeneas)]

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

trait Ord {
    fn cmp(&self, other: &Self) -> Ordering;
}

struct Node<T> {
    value: T,
    left: Tree<T>,
    right: Tree<T>,
}

type Tree<T> = Option<Box<Node<T>>>;

struct TreeSet<T> {
    root: Tree<T>,
}

impl<T: Ord> TreeSet<T> {
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
    pub fn insert(&mut self, value: T) -> bool {
        let mut current_tree = &mut self.root;

        while let Some(current_node) = current_tree {
            match current_node.value.cmp(&value) {
                Ordering::Less => current_tree = &mut current_node.right,
                Ordering::Equal => return false,
                Ordering::Greater => current_tree = &mut current_node.left,
            }
        }

        *current_tree = Some(Box::new(Node {
            value,
            left: None,
            right: None,
        }));

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    trait Bounded {
        type Value;
        fn max_value() -> Self::Value;
        fn min_value() -> Self::Value;
    }

    impl Bounded for i32 {
        type Value = i32;
        fn min_value() -> i32 {
            i32::MIN
        }
        fn max_value() -> i32 {
            i32::MAX
        }
    }

    impl<T: Bounded<Value = T> + Ord + Copy> Node<T> {
        fn check_bst_inv(&self, min: T, max: T) -> bool {
            matches!(self.value.cmp(&min), Ordering::Greater)
                && matches!(self.value.cmp(&max), Ordering::Less)
                && self
                    .left
                    .as_ref()
                    .map_or(true, |left| left.check_bst_inv(min, self.value))
                && self
                    .right
                    .as_ref()
                    .map_or(true, |right| right.check_bst_inv(self.value, max))
        }
    }

    impl<T: Bounded<Value = T> + Ord + Copy> TreeSet<T> {
        fn check_bst_inv(&self) -> bool {
            self.root
                .as_ref()
                .map_or(true, |r| r.check_bst_inv(T::min_value(), T::max_value()))
        }
    }

    #[test]
    fn unbalanced_right() {
        let mut t: TreeSet<i32> = TreeSet::new();
        for i in 0..100 {
            t.insert(i);
            t.check_bst_inv();
        }

        assert!(
            t.find(50),
            "Unexpectedly failed to find the 50 value in the tree"
        );

        assert!(!t.find(-50), "Unexpectedly find the -50 value in the tree");
    }

    #[test]
    fn unbalanced_left() {
        let mut t: TreeSet<i32> = TreeSet::new();
        for i in -100..0 {
            t.insert(i);
            t.check_bst_inv();
        }

        assert!(
            t.find(-50),
            "Unexpectedly failed to find the -50 value in the tree"
        );

        assert!(!t.find(50), "Unexpectedly find the 50 value in the tree");
    }

    #[test]
    fn right_left_unbalanced() {
        let mut t: TreeSet<i32> = TreeSet::new();
        for i in 0..100 {
            t.insert(i);
            t.check_bst_inv();
        }
        for i in -100..0 {
            t.insert(i);
            t.check_bst_inv();
        }

        assert!(
            t.find(-50),
            "Unexpectedly failed to find the -50 value in the tree"
        );
        assert!(
            t.find(50),
            "Unexpectedly failed to find the 50 value in the tree"
        );
    }
}
