import Avl.Extracted

namespace Tree

variable {T: Type}

open avl_verification

-- Otherwise, Lean cannot prove termination by itself.
@[reducible]
def AVLTree (U: Type) := Option (AVLNode U)
def AVLTree.nil: AVLTree T := none

def AVLTree.val (t: AVLTree T): Option T := match t with
| none => none
| some (AVLNode.mk x _ _ _) => some x

@[simp]
lemma AVLTree.val_of_mk {x: T} {left right: AVLTree T}: AVLTree.val (AVLNode.mk x left right h) = .some x := rfl

def AVLTree.left (t: AVLTree T): AVLTree T := match t with
| none => none
| some (AVLNode.mk _ left _ _) => left

@[simp]
lemma AVLTree.left_of_mk {x: T} {left right: AVLTree T}: AVLTree.left (AVLNode.mk x left right h) = left := rfl

def AVLTree.right (t: AVLTree T): AVLTree T := match t with
| none => none
| some (AVLNode.mk _ _ right _) => right

@[simp]
lemma AVLTree.right_of_mk {x: T} {left right: AVLTree T}: AVLTree.right (AVLNode.mk x left right h) = right := rfl

def AVLTree.memoized_height (t: AVLTree T): Primitives.Scalar .Usize := match t with
| none => 0#usize
| some (AVLNode.mk _ _ _ h) => h

def AVLNode.left (t: AVLNode T): AVLTree T := match t with
| AVLNode.mk _ left _ _ => left

@[simp]
lemma AVLTree.left_of_some {t: AVLNode T}: AVLTree.left (some t) = AVLNode.left t := by cases t; simp [AVLNode.left]

@[simp]
lemma AVLNode.left_of_mk {x: T} {left right: AVLTree T}: AVLNode.left (AVLNode.mk x left right h) = left := rfl

def AVLNode.right (t: AVLNode T): AVLTree T := match t with
| AVLNode.mk _ _ right _ => right

@[simp]
lemma AVLTree.right_of_some {t: AVLNode T}: AVLTree.right (some t) = AVLNode.right t := by cases t; simp [AVLNode.right]

@[simp]
lemma AVLNode.right_of_mk {x: T} {left right: AVLTree T}: AVLNode.right (AVLNode.mk x left right h) = right := rfl

def AVLNode.val (t: AVLNode T): T := match t with
| AVLNode.mk x _ _ _ => x

@[simp]
lemma AVLNode.val_of_mk {x: T} {left right: AVLTree T}: AVLNode.val (AVLNode.mk x left right h) = x := rfl

def AVLNode.memoized_height (t: AVLNode T): Primitives.Scalar .Usize := match t with 
| AVLNode.mk _ _ _ h => h

mutual
def AVLTree.height_node: AVLNode T -> Nat
| AVLNode.mk y left right _ => 1 + max (AVLTree.height left) (AVLTree.height right)

def AVLTree.height: AVLTree T -> Nat
| none => 0
| some n => AVLTree.height_node n
end

@[simp]
def AVLTree.height_of_none: @AVLTree.height T none = 0 := rfl

@[simp]
def AVLTree.height_of_some {t: AVLNode T}: AVLTree.height (some t) = AVLTree.height_node t := by simp [AVLTree.height]

@[simp]
def AVLTree.height_node_of_mk {left right: AVLTree T}: AVLTree.height_node (AVLNode.mk x left right h) = 1 + max (AVLTree.height left) (AVLTree.height right) := by simp [AVLTree.height_node]

def AVLTree.height_node_eq (t: AVLNode T): AVLTree.height_node t = 1 + max (AVLTree.height (AVLNode.left t)) (AVLTree.height (AVLNode.right t)) := by sorry

def AVLNode.height_left_lt_tree (left: AVLNode T) {right: AVLTree T}: AVLTree.height_node left < AVLTree.height_node (AVLNode.mk x (some left) right h) := by 
  simp only [AVLTree.height_node_of_mk, AVLTree.height_of_some]
  rw [Nat.add_comm, Nat.add_one]
  exact Nat.lt_succ_of_le (le_max_left _ _)

def AVLNode.height_right_lt_tree (right: AVLNode T) {left: AVLTree T}: AVLTree.height_node right < AVLTree.height_node (AVLNode.mk x left (some right) h) := by 
  simp only [AVLTree.height_node_of_mk, AVLTree.height_of_some]
  rw [Nat.add_comm, Nat.add_one]
  exact Nat.lt_succ_of_le (le_max_right _ _)

def AVLTree.height_left_lt_tree (left right: AVLTree T): AVLTree.height left < AVLTree.height (some (AVLNode.mk x left right h)) := by 
  match left with 
  | none => simp [height, height_node]
  | some left => simp only [height, AVLNode.height_left_lt_tree left]

def AVLTree.height_left_lt_tree' (t: AVLNode T): AVLTree.height (AVLNode.left t) < AVLTree.height (some t) := by 
  match t with 
  | AVLNode.mk _ left right h => simp only [AVLNode.left, AVLTree.height_left_lt_tree]

def AVLTree.height_left_le_tree' (t: AVLTree T): AVLTree.height (AVLTree.left t) ≤ AVLTree.height t := by 
  match t with 
  | none => simp [height, left]
  | some t => simp only [AVLTree.left_of_some, le_of_lt (AVLTree.height_left_lt_tree' t)]

def AVLTree.height_right_lt_tree (left right: AVLTree T): AVLTree.height right < AVLTree.height (some (AVLNode.mk x left right h)) := by 
  match right with 
  | none => simp [height, height_node]
  | some right => simp only [height, AVLNode.height_right_lt_tree right]

def AVLTree.height_right_lt_tree' (t: AVLNode T): AVLTree.height (AVLNode.right t) < AVLTree.height (some t) := by 
  match t with 
  | AVLNode.mk _ left right h => simp only [AVLNode.right, AVLTree.height_right_lt_tree]


def AVLTreeSet.nil: AVLTreeSet T := { root := AVLTree.nil }

-- Automatic synthesization of this seems possible at the Lean level?
instance: Inhabited (AVLTree T) where
  default := AVLTree.nil

instance: Inhabited (AVLTreeSet T) where
  default := AVLTreeSet.nil

instance: Coe (Option (AVLNode T)) (AVLTree T) where
  coe x := x

-- TODO: ideally, it would be nice if we could generalize
-- this to any `BinaryTree` typeclass.

def AVLTree.mem (tree: AVLTree T) (x: T) :=
  match tree with
  | none => False
  | some (AVLNode.mk y left right _) => x = y ∨ AVLTree.mem left x ∨ AVLTree.mem right x

@[simp]
def AVLTree.mem_none: AVLTree.mem none = ({}: Set T) := rfl

@[simp]
def AVLTree.mem_some {x: T} {left right: AVLTree T}: AVLTree.mem (some (AVLNode.mk x left right h)) = (({x}: Set T) ∪ AVLTree.mem left ∪ AVLTree.mem right) := by
  ext y
  rw [AVLTree.mem]
  simp [Set.insert_union]
  simp [Set.insert_def, Set.setOf_set, Set.mem_def, Set.union_def]

-- TODO(reinforcement): ∪ is actually disjoint if we prove this is a binary search tree.

def AVLTree.set (t: AVLTree T): Set T := _root_.setOf (AVLTree.mem t)

@[simp]
def AVLTree.set_some {x: T} {left right: AVLTree T}: AVLTree.set (some (AVLNode.mk x left right h)) = {x} ∪ AVLTree.set left ∪ AVLTree.set right := by 
  simp [set, setOf]

end Tree
