//@ [!lean] skip
//@ [lean] aeneas-args=-split-files -no-gen-lib-entry
// ^ the `-no-gen-lib-entry` is because we add a custom import in the Avl.lean file: we do not
// want to overwrite it.
#![feature(register_tool)]
#![register_tool(aeneas)]

fn max<T: Ord + Copy>(a: T, b: T) -> T {
    match a.cmp(&b) {
        Ordering::Less => b,
        Ordering::Equal => b,
        Ordering::Greater => a,
    }
}

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

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub trait Ord {
    fn cmp(&self, other: &Self) -> Ordering;
}

struct AVLNode<T> {
    value: T,
    left: Option<Box<AVLNode<T>>>,
    right: Option<Box<AVLNode<T>>>,
    height: usize,
}

pub struct AVLTree<T> {
    root: Option<Box<AVLNode<T>>>,
}

impl<T> AVLNode<T> {
    fn update_height(&mut self) {
        self.height = 1 + max(self.left_height(), self.right_height());
    }

    fn left_height(&self) -> usize {
        if let Some(ref left) = self.left {
            left.height
        } else {
            0
        }
    }

    fn right_height(&self) -> usize {
        if let Some(ref right) = self.right {
            right.height
        } else {
            0
        }
    }

    fn balance_factor(&self) -> i8 {
        let left_height = self.left_height();
        let right_height = self.right_height();

        if left_height >= right_height {
            (left_height - right_height) as i8
        } else {
            -((right_height - left_height) as i8)
        }
    }

    fn rotate_right(&mut self) -> bool {
        if self.left.is_none() {
            return false;
        }

        if let Some(ref mut left_node) = self.left {
            let left_right_tree = left_node.right.take();
            let left_left_tree = left_node.left.take();

            let mut new_right_tree = std::mem::replace(&mut self.left, left_left_tree);
            if let Some(ref mut new_right_tree) = new_right_tree {
                std::mem::swap(&mut self.value, &mut new_right_tree.value);
            } else {
                panic!();
            }

            let right_tree = self.right.take();

            if let Some(ref mut new_right_node) = new_right_tree {
                new_right_node.left = left_right_tree;
                new_right_node.right = right_tree;
            } else {
                panic!();
            }

            self.right = new_right_tree;

            if let Some(ref mut node) = self.right {
                node.update_height();
            }

            self.update_height();

            true
        } else {
            panic!();
        }
    }

    fn rotate_left(&mut self) -> bool {
        if self.right.is_none() {
            return false;
        }

        if let Some(ref mut right_node) = self.right {
            let right_left_tree = right_node.left.take();
            let right_right_tree = right_node.right.take();

            let mut new_left_tree = std::mem::replace(&mut self.right, right_right_tree);
            if let Some(ref mut new_left_tree) = new_left_tree {
                std::mem::swap(&mut self.value, &mut new_left_tree.value);
            } else {
                panic!();
            }
            let left_tree = self.left.take();

            if let Some(ref mut new_left_node) = new_left_tree {
                new_left_node.right = right_left_tree;
                new_left_node.left = left_tree;
            } else {
                panic!();
            }

            self.left = new_left_tree;

            if let Some(ref mut node) = self.left {
                node.update_height();
            }

            self.update_height();

            true
        } else {
            panic!();
        }
    }

    fn rebalance(&mut self) {
        match self.balance_factor() {
            -2 => {
                if let Some(ref mut right_node) = self.right {
                    if right_node.balance_factor() == 1 {
                        right_node.rotate_right();
                    }
                } else {
                    panic!();
                }

                self.rotate_left();
            }
            2 => {
                if let Some(ref mut left_node) = self.left {
                    if left_node.balance_factor() == -1 {
                        left_node.rotate_left();
                    }
                } else {
                    panic!();
                }

                self.rotate_right();
            }
            _ => (),
        }
    }
}

impl<T: Ord> AVLNode<T> {
    fn insert(&mut self, value: T) -> bool {
        let ordering = self.value.cmp(&value);
        match ordering {
            Ordering::Less => AVLTree::insert_in_opt_node(&mut self.left, value),
            Ordering::Equal => false,
            Ordering::Greater => AVLTree::insert_in_opt_node(&mut self.right, value),
        }
    }
}

impl<T: Ord> AVLTree<T> {
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

    fn insert_in_opt_node(node: &mut Option<Box<AVLNode<T>>>, value: T) -> bool {
        match *node {
            Some(node) => {
                let inserted = node.insert(value);
                if inserted {
                    node.rebalance();
                }
                inserted
            }
            None => {
                *node = Some(Box::new(AVLNode {
                    value,
                    left: None,
                    right: None,
                    height: 0,
                }));
                true
            }
        }
    }

    /// Insert a value and return [true] if the value was not already there.
    pub fn insert(&mut self, value: T) -> bool {
        AVLTree::insert_in_opt_node(&mut self.root, value)
    }
}
