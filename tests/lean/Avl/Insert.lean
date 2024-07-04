import Avl.Tree
import Avl.AVL
import Avl.BinarySearchTree
import Avl.Specifications

namespace Implementation

open Primitives
open avl
open Tree (AVLTree AVLTree.set)
open Specifications (OrdSpecLinearOrderEq infallible ltOfRustOrder gtOfRustOrder)

variable (T: Type) (H: avl.Ord T) [LinearOrder T] (Ospec: OrdSpecLinearOrderEq H)

@[pspec]
theorem AVLTreeSet.insert_loop_spec_local (p: T -> Prop)
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ok o)
  (a: T) (t: Option (AVLNode T)):
  ∃ added t_new, AVLTreeSet.insert_loop T H a t = Result.ok ⟨ added, t_new ⟩
--  ∧ AVLTree.set t'.2 = insert a (AVLTree.set t)
  ∧ (BST.ForallNode p t -> p a -> BST.ForallNode p t_new)
  ∧ (AVLTree.isAVL t -> AVLTree.isAVL t_new)
  := by match t with
  | none =>
    simp [AVLTreeSet.insert_loop, AVLTree.set, setOf]
    split_conjs
    intros _ Hpa
    constructor; all_goals try simp [BST.ForallNode.none]
    exact Hpa
    simp [AVLTree.isAVL, AVLTree.balancingFactor]
  | some (AVLNode.mk b left right h) =>
    rw [AVLTreeSet.insert_loop]
    simp only []
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals simp only []
    {
      progress keep Htree as ⟨ added₁, right₁, Hnode ⟩ -- deep destructure is not working
      rcases Hnode with ⟨ Hnode, Havl ⟩
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left right₁), _ ⟩ ⟩
      simp only [true_and]
      split_conj
      intros Hptree Hpa
      constructor
      exact Hptree.left
      exact Hptree.label
      exact Hnode Hptree.right Hpa
      intro Havl_tree
      simp [AVLTree.isAVL, AVLTree.balancingFactor]
    }
    {
      simp; tauto
    }
    {
      -- TODO: investigate wlog.
      -- Symmetric case of left.
      progress keep Htree as ⟨ added₁, left₁, Hnode ⟩
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left₁ right), _ ⟩ ⟩
      simp only [true_and]
      intros Hptree Hpa
      constructor
      exact Hnode Hptree.left Hpa
      exact Hptree.label
      exact Hptree.right
    }

@[pspec]
lemma AVLTreeSet.insert_loop_spec_global
  (a: T) (t: Option (AVLNode T))
  :
  BST.Invariant t -> ∃ added t_new, AVLTreeSet.insert_loop T H a t = Result.ok ⟨ added, t_new ⟩
  ∧ BST.Invariant t_new ∧ AVLTree.set t_new = {a} ∪ AVLTree.set t := by
  intro Hbst
  match t with
  | none => simp [AVLTreeSet.insert_loop, AVLTree.set, setOf]
  | some (AVLNode.mk b left right _) =>
    rw [AVLTreeSet.insert_loop]
    simp only []
    have : ∀ a b, ∃ o, H.cmp a b = .ok o := infallible H
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals simp only []
    {
      have ⟨ added₂, right₂, ⟨ H_result, ⟨ H_bst, H_set ⟩ ⟩ ⟩ := AVLTreeSet.insert_loop_spec_global a right (BST.right Hbst)
      progress keep Htree with AVLTreeSet.insert_loop_spec_local as ⟨ added₁, right₁, Hnode ⟩
      exact (fun x => b < x)
      rewrite [Htree] at H_result; simp at H_result
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left right₁), _ ⟩ ⟩
      simp only [true_and]
      split_conjs
      cases' Hbst with _ _ _ H_forall_left H_forall_right H_bst_left H_bst_right
      constructor
      exact H_forall_left
      apply Hnode; exact H_forall_right
      exact (ltOfRustOrder H b a Hordering)
      exact H_bst_left
      convert H_bst
      exact H_result.2
      simp [AVLTree.set_some]
      rewrite [H_result.2, H_set]
      simp
    }
    {
      simp; split_conjs
      . tauto
      . simp [Ospec.equivalence _ _ Hordering]
    }
    {
      have ⟨ added₂, left₂, ⟨ H_result, ⟨ H_bst, H_set ⟩ ⟩ ⟩ := AVLTreeSet.insert_loop_spec_global a left (BST.left Hbst)
      progress keep Htree with AVLTreeSet.insert_loop_spec_local as ⟨ added₁, left₁, Hnode ⟩
      exact (fun x => x < b)
      rewrite [Htree] at H_result; simp at H_result
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left₁ right), _ ⟩ ⟩
      simp only [true_and]
      split_conjs
      cases' Hbst with _ _ _ H_forall_left H_forall_right H_bst_left H_bst_right
      constructor
      apply Hnode; exact H_forall_left
      exact (gtOfRustOrder H b a Hordering)
      exact H_forall_right
      convert H_bst
      exact H_result.2
      exact H_bst_right
      simp [AVLTree.set_some]
      rewrite [H_result.2, H_set]
      simp [Set.singleton_union, Set.insert_comm, Set.insert_union]
    }

@[pspec]
def AVLTreeSet.insert_spec
  (a: T) (t: AVLTreeSet T):
  BST.Invariant t.root -> (∃ t' added,t.insert _ H a = Result.ok (added, t')
  -- it's still a binary search tree.
  ∧ BST.Invariant t'.root
  ∧ AVLTree.set t'.root = {a} ∪ AVLTree.set t.root)
  := by
  rw [AVLTreeSet.insert]; intro Hbst
  progress keep h as ⟨ t', Hset ⟩;
  simp; assumption

end Implementation
