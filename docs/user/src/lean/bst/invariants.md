# Invariants of a binary search tree

The binary search tree invariant \\( \textrm{BST}(T) \\) can be defined inductively:

- \\( \textrm{BST}(\emptyset) \\) where \\( \emptyset \\) is the empty binary tree
- yadayada

Mirroring this mathematical definition in the Lean theorem prover yields to an inductive predicate:

```lean
-- A helper inductive predicate over trees

inductive ForallNode (p: T -> Prop): Tree T -> Prop
| none : ForallNode p none
| some (a: T) (left: Tree T) (right: Tree T) : ForallNode p left -> p a -> ForallNode p right -> ForallNode p (some (Node.mk a left right))

--- To express inequalities between values of `T`, it is necessary to require an linear order (also known as total order) over `T`.
variable [LinearOrder T]
inductive Invariant: Tree T -> Prop
| none : Invariant none
| some (a: T) (left: Tree T) (right: Tree T) : 
  ForallNode (fun v => v < a) left -> ForallNode (fun v => a < v) right
  -> Invariant left -> Invariant right -> Invariant (some (Node.mk a left right))
```

Once those definitions are provided, helper theorems on `ForallNode` and `Invariant` will be useful.

As exercises, consider proving the following statements:

- `ForallNode.not_mem {a: T} (p: T -> Prop) (t: Option (Node T)): ¬ p a -> ForallNode p t -> a ∉ Tree.set t`: given an element \\( a \\) and a predicate \\( p \\), if \\( \lnot p(a) \\) but all the nodes in the tree \\( t \\) verifies the predicate \\( p \\), then \\( a \\) cannot be part of that tree.
- `singleton_bst {a: T}: Invariant (some (Node.mk a none none))` : the "singleton" tree, i.e. a tree with no subtrees, is a binary search tree.
- `left_pos {left right: Option (Node T)} {a x: T}: BST.Invariant (some (Node.mk a left right)) -> x ∈ Tree.set (Node.mk a left right) -> x < a -> x ∈ Tree.set left`, that is a sub-tree localisation theorem by comparing \\( x \\) to the root.
