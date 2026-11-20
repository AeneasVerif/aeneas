//@ [!lean] skip
// `Branch` is mutually recursive with `Node`, so it is not extracted as a Lean
// structure and gets explicit field projectors. Their record argument must be
// applied to the const generic `N`.

pub enum Node<const N: usize> {
    Leaf(u32),
    Branch(Box<Branch<N>>),
}

pub struct Branch<const N: usize> {
    pub keys: Vec<u32>,
    pub children: Vec<Node<N>>,
}

pub fn num_children<const N: usize>(b: &Branch<N>) -> usize {
    b.children.len()
}
