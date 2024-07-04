import Avl.Tree

namespace BST

open Primitives (Result Scalar)
open avl (AVLNode Ordering)
open Tree (AVLTree AVLNode.left AVLNode.right AVLNode.val)

-- TODO: build a function to build a tree out of a left and right
-- with automatic height computation?

@[reducible]
def AVLNode.mk' (a: T) (left: AVLTree T) (right: AVLTree T): AVLNode T :=
  let height := 1 + max left.height right.height
  -- TODO: Scalar.ofNat would be nice...
  -- discharge the proof by bounding left & right's height all the time... ?
  -- Interesting remark:
  -- Lean can support trees of arbitrary height
  -- Rust cannot because the height computation will overflow at some point, Rust can only do with trees with representable (usize) height.
  -- It's not big deal because the maximally sized tree is bigger than what modern computer can store at all (exabyte-sized tree).
  AVLNode.mk a left right (@Scalar.ofInt _ height (by sorry))

inductive ForallNode (p: T -> Prop): AVLTree T -> Prop
| none : ForallNode p none
| some (a: T) (left: AVLTree T) (right: AVLTree T) : ForallNode p left -> p a -> ForallNode p right -> ForallNode p (some (AVLNode.mk a left right h))

theorem ForallNode.left {p: T -> Prop} {t: AVLTree T}: ForallNode p t -> ForallNode p t.left := by
  intro Hpt
  cases Hpt with
  | none => simp [AVLTree.left, ForallNode.none]
  | some a left right f_pleft f_pa f_pright => simp [AVLTree.left, f_pleft]

theorem ForallNode.right {p: T -> Prop} {t: AVLTree T}: ForallNode p t -> ForallNode p t.right := by
  intro Hpt
  cases Hpt with
  | none => simp [AVLTree.right, ForallNode.none]
  | some a left right f_pleft f_pa f_pright => simp [AVLTree.right, f_pright]

theorem ForallNode.label {a: T} {p: T -> Prop} {left right: AVLTree T}: ForallNode p (AVLNode.mk a left right h) -> p a := by
  intro Hpt
  cases Hpt with
  | some a left right f_pleft f_pa f_pright => exact f_pa

theorem ForallNode.not_mem {a: T} (p: T -> Prop) (t: Option (AVLNode T)): ¬ p a -> ForallNode p t -> a ∉ AVLTree.set t := fun Hnpa Hpt => by
  cases t with
  | none => simp [AVLTree.set]; tauto
  | some t =>
    cases Hpt with
    | some b left right f_pbleft f_pb f_pbright =>
      simp [AVLTree.set_some]
      push_neg
      split_conjs
      . by_contra hab; rw [hab] at Hnpa; exact Hnpa f_pb
      . exact ForallNode.not_mem p left Hnpa f_pbleft
      . exact ForallNode.not_mem p right Hnpa f_pbright

theorem ForallNode.not_mem' {a: T} (p: T -> Prop) (t: Option (AVLNode T)): p a -> ForallNode (fun x =>  ¬p x) t -> a ∉ AVLTree.set t := fun Hpa Hnpt => by
  refine' ForallNode.not_mem (fun x => ¬ p x) t _ _
  simp [Hpa]
  exact Hnpt

theorem ForallNode.imp {p q: T -> Prop} {t: AVLTree T}: (∀ x, p x -> q x) -> ForallNode p t -> ForallNode q t := fun Himp Hpt => by
  induction Hpt
  . simp [ForallNode.none]
  . constructor
    . assumption
    . apply Himp; assumption
    . assumption

-- This is the binary search invariant.
variable [LinearOrder T]
inductive Invariant: AVLTree T -> Prop
| none : Invariant none
| some (a: T) (left: AVLTree T) (right: AVLTree T) :
  ForallNode (fun v => v < a) left -> ForallNode (fun v => a < v) right
  -> Invariant left -> Invariant right -> Invariant (some (AVLNode.mk a left right h))

@[simp]
theorem singleton_bst {a: T}: Invariant (some (AVLNode.mk a none none h)) := by
  apply Invariant.some
  all_goals simp [ForallNode.none, Invariant.none]

theorem left {t: AVLTree T}: Invariant t -> Invariant t.left := by
  intro H
  induction H with
  | none => exact Invariant.none
  | some _ _ _ _ _ _ _ _ _ => simp [AVLTree.left]; assumption

theorem right {t: AVLTree T}: Invariant t -> Invariant t.right := by
  intro H
  induction H with
  | none => exact Invariant.none
  | some _ _ _ _ _ _ _ _ _ => simp [AVLTree.right]; assumption

-- TODO: ask at most for LT + Irreflexive (lt_irrefl) + Trichotomy (le_of_not_lt)?
theorem left_pos {left right: Option (AVLNode T)} {a x: T}: BST.Invariant (some (AVLNode.mk a left right h)) -> x ∈ AVLTree.set (AVLNode.mk a left right h) -> x < a -> x ∈ AVLTree.set left := fun Hbst Hmem Hxa => by
   simp [AVLTree.set_some] at Hmem
   rcases Hmem with (Heq | Hleft) | Hright
   . rewrite [Heq] at Hxa; exact absurd Hxa (lt_irrefl _)
   . assumption
   . exfalso

     -- Hbst -> x ∈ right -> ForallNode (fun v => ¬ v < a)
     refine' ForallNode.not_mem' (fun v => v < a) right Hxa _ _
     simp [le_of_not_lt]
     cases Hbst with
     | some _ _ _ _ Hforall _ =>
       refine' ForallNode.imp _ Hforall
       exact fun x => le_of_lt
     assumption

theorem right_pos {left right: Option (AVLNode T)} {a x: T}: BST.Invariant (some (AVLNode.mk a left right h)) -> x ∈ AVLTree.set (AVLNode.mk a left right h) -> a < x -> x ∈ AVLTree.set right := fun Hbst Hmem Hax => by
   simp [AVLTree.set_some] at Hmem
   rcases Hmem with (Heq | Hleft) | Hright
   . rewrite [Heq] at Hax; exact absurd Hax (lt_irrefl _)
   . exfalso
     refine' ForallNode.not_mem' (fun v => a < v) left Hax _ _
     simp [le_of_not_lt]
     cases Hbst with
     | some _ _ _ Hforall _ _ =>
       refine' ForallNode.imp _ Hforall
       exact fun x => le_of_lt
     assumption
   . assumption


end BST
