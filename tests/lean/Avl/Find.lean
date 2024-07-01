import Avl.Tree
import Avl.BinarySearchTree
import Avl.Specifications
import Avl.Extracted

namespace Implementation

open Primitives
open avl_verification
open Tree (AVLTree AVLTree.set)
open Specifications (OrdSpecLinearOrderEq infallible ltOfRustOrder gtOfRustOrder)

variable (T: Type) (H: avl_verification.Ord T) [DecidableEq T] [LinearOrder T] (Ospec: OrdSpecLinearOrderEq H)

@[pspec]
def AVLTreeSet.find_loop_spec
  (a: T) (t: Option (AVLNode T)):
  BST.Invariant t -> ∃ b, AVLTreeSet.find_loop _ H a t = Result.ok b ∧ (b ↔ a ∈ AVLTree.set t) := fun Hbst => by
  rewrite [AVLTreeSet.find_loop]
  match t with 
  | none => use false; simp [AVLTree.set]; tauto
  | some (AVLNode.mk b left right _) =>
    dsimp only
    have : ∀ a b, ∃ o, H.cmp a b = .ok o := infallible H
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals dsimp only
    . convert (AVLTreeSet.find_loop_spec a right (BST.right Hbst)) using 4
      apply Iff.intro
      -- We apply a localization theorem here.
      . intro Hmem; exact (BST.right_pos Hbst Hmem (ltOfRustOrder _ _ _ Hordering))
      . intro Hmem; simp [AVLTree.set_some]; right; assumption
    . simp [Ospec.equivalence _ _ Hordering]
    . convert (AVLTreeSet.find_loop_spec a left (BST.left Hbst)) using 4
      apply Iff.intro
      -- We apply a localization theorem here.
      . intro Hmem; exact (BST.left_pos Hbst Hmem (gtOfRustOrder _ _ _ Hordering))
      . intro Hmem; simp [AVLTree.set_some]; left; right; assumption


def AVLTreeSet.find_spec
  (a: T) (t: AVLTreeSet T):
  BST.Invariant t.root -> ∃ b, t.find _ H a = Result.ok b ∧ (b ↔ a ∈ AVLTree.set t.root) := fun Hbst => by
    rw [AVLTreeSet.find]
    progress; simp only [Result.ok.injEq, exists_eq_left']; assumption

end Implementation

