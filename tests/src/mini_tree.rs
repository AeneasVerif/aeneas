//@ [coq,fstar] skip

struct Node {
    child: OptNode,
}

type OptNode = Option<Box<Node>>;

struct Tree {
    root: OptNode,
}

impl Tree {
    pub fn explore(&self) {
        let mut current_tree = &self.root;

        while let Some(current_node) = current_tree {
            current_tree = &current_node.child
        }
    }
}
