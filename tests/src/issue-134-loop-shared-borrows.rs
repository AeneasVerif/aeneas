//@ [!lean] skip

struct AVLNode {
    child: Option<Box<AVLNode>>,
}

struct AVLTreeSet {
    root: Option<Box<AVLNode>>,
}

impl AVLNode {
    pub fn find(self) -> bool {
        let mut current_tree = &self.child; // This is the root of the problem in the computation of the fixed point

        while let Some(current_node) = current_tree {
            current_tree = &current_node.child;
        }

        false
    }
}
