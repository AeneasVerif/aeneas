-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [bst]: function definitions
import Aeneas
import Bst.Types
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace bst

/- [bst::{bst::TreeSet<T>}::new]:
   Source: 'src/bst.rs', lines 28:4-30:5 -/
def TreeSet.new {T : Type} (OrdInst : Ord T) : Result (TreeSet T) :=
  ok { root := none }

/- [bst::{bst::TreeSet<T>}::find]: loop 0:
   Source: 'src/bst.rs', lines 35:8-44:5 -/
divergent def TreeSet.find_loop
  {T : Type} (OrdInst : Ord T) (value : T) (current_tree : Option (Node T)) :
  Result Bool
  :=
  match current_tree with
  | none => ok false
  | some current_node =>
    do
    let o ← OrdInst.cmp current_node.value value
    match o with
    | Ordering.Less => TreeSet.find_loop OrdInst value current_node.right
    | Ordering.Equal => ok true
    | Ordering.Greater => TreeSet.find_loop OrdInst value current_node.left

/- [bst::{bst::TreeSet<T>}::find]:
   Source: 'src/bst.rs', lines 32:4-44:5 -/
@[reducible]
def TreeSet.find
  {T : Type} (OrdInst : Ord T) (self : TreeSet T) (value : T) : Result Bool :=
  TreeSet.find_loop OrdInst value self.root

/- [bst::{bst::TreeSet<T>}::insert]: loop 0:
   Source: 'src/bst.rs', lines 48:8-63:5 -/
divergent def TreeSet.insert_loop
  {T : Type} (OrdInst : Ord T) (value : T) (current_tree : Option (Node T)) :
  Result (Bool × (Option (Node T)))
  :=
  match current_tree with
  | none => let n := Node.mk value none none
            ok (true, some n)
  | some current_node =>
    do
    let o ← OrdInst.cmp current_node.value value
    match o with
    | Ordering.Less =>
      do
      let (b, current_tree1) ←
        TreeSet.insert_loop OrdInst value current_node.right
      ok (b, some (Node.mk current_node.value current_node.left current_tree1))
    | Ordering.Equal => ok (false, current_tree)
    | Ordering.Greater =>
      do
      let (b, current_tree1) ←
        TreeSet.insert_loop OrdInst value current_node.left
      ok (b, some (Node.mk current_node.value current_tree1
        current_node.right))

/- [bst::{bst::TreeSet<T>}::insert]:
   Source: 'src/bst.rs', lines 45:4-63:5 -/
def TreeSet.insert
  {T : Type} (OrdInst : Ord T) (self : TreeSet T) (value : T) :
  Result (Bool × (TreeSet T))
  :=
  do
  let (b, ts) ← TreeSet.insert_loop OrdInst value self.root
  ok (b, { root := ts })

end bst
