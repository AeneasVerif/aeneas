import Avl.Funs
import Avl.Types
-- TODO: merge into Spec.lean

namespace avl

variable {T: Type}

abbrev Child T := Option (Node T)

-- TODO: rename to node_height
mutual
@[simp]
def Node.compute_height: Node T -> Nat
| Node.mk y left right _ => 1 + max (Child.compute_height left) (Child.compute_height right)

@[simp]
def Child.compute_height: Child T -> Nat
| none => 0
| some n => Node.compute_height n
end

mutual
@[simp]
def Node.size: Node T -> Nat
| Node.mk y left right _ => 1 + Child.size left + Child.size right

@[simp]
def Child.size: Child T -> Nat
| none => 0
| some n => 1 + Node.size n
end

def Tree.nil: Tree T := { root := none }

-- Automatic synthesization of this seems possible at the Lean level?
instance: Inhabited (Tree T) where
  default := Tree.nil

instance [Inhabited T]: Inhabited (Node T) where
  default := ⟨ Inhabited.default, none, none, 0#usize ⟩

mutual
@[simp, reducible] def Child.v (tree: Child T) : Set T :=
  match tree with
  | none => ∅
  | some node => node.v

@[simp, reducible] def Node.v (node : Node T) : Set T :=
  match node with
  | .mk x left right _ => {x} ∪ Child.v left ∪ Child.v right
end

@[reducible]
def Tree.v (t: Tree T): Set T := Child.v t.root

end avl
