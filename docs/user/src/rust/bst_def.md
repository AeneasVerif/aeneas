# Defining Binary Search Trees in Rust

## Pre-requisites

Due to Aeneas limitations, we will not use Rust standard library for the order definitions, e.g. `Ord` / `Ordering`.

We will define ours and we will also take them into account in the verification:

```rust,noplayground
pub enum Ordering {
    Less,
    Equal,
    Greater,
}

trait Ord {
    fn cmp(&self, other: &Self) -> Ordering;
}

impl Ord for u32 {
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
```

We will revisit those definitions in the chapter about mathematical representations because we will need to decide what extra properties we want to impose on an `Ord` as Rust allows many degenerate implementations of an order which will not lead to a working binary search tree.

## Data structure

We define trees in Rust following borrow checker constraints, e.g. a `Box` indirection is required.

```rust,noplayground
struct Node<T> {
   value: T,
   left: Option<Box<Node<T>>,
   right: Option<Box<Node<T>>
}

type Tree<T> = Option<Box<Node<T>>>;
```

**Note**: `Box` is erased during translation, i.e. in Lean, no details about `Box` will be available.

**Note 2** : We do not ask for `T` to have `Ord`, we will put this trait bound on the functions in the next section.

## Operations on trees

We will define two operations for this guide:

- `height`, defined by: $$\textrm{height}(t) = 1 + \textrm{max}(\textrm{height}(t.\textrm{left}), \textrm{height}(t.\textrm{right}))$$
- `insert` which inserts an item inside the binary search tree

**Note** : Due to Aeneas limitations, we sometimes have to rewrite the code in a way that will be possible to extract to Lean, those situations are documented with a comment to explain why it is necessary.

## `insert`

We will need to define a container for our tree to hold our root:

```rust,noplayground
struct TreeSet<T> {
   root: Tree<T>
}

impl<T: Ord> TreeSet<T> {
    pub fn new() -> Self {
        Self { root: None }
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
```

`insert` returns whether the item was already in or not and mutates in-place the tree.

## `find`

```rust,noplayground
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
```

We return whether we find the item or not in the tree by browsing it using the binary search tree invariant.
