import Avl.Tree

open Tree (AVLTree)

namespace Tree

variable {T: Type}

open avl

def AVLTree.balancingFactor (t: AVLTree T): ℤ := match t with
| .none => 0
| .some (AVLNode.mk _ left right _) => AVLTree.height left - AVLTree.height right

lemma AVLTree.balancingFactor_eq (t: AVLTree T): AVLTree.balancingFactor t = AVLTree.height (AVLTree.left t) - AVLTree.height (AVLTree.right t) := by sorry

@[simp]
lemma AVLTree.balancingFactor_some (left right: AVLTree T): AVLTree.balancingFactor (some (AVLNode.mk x left right h)) = AVLTree.height left - AVLTree.height right := by rfl

def AVLTree.isAVL (t: AVLTree T): Prop := |t.balancingFactor| <= 1

end Tree
