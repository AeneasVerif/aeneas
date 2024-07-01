import Avl.Extracted
import Avl.Tree
import Avl.BinarySearchTree

namespace Implementation

variable {T: Type}

open avl_verification
open Primitives
open Tree (AVLTree AVLNode.left AVLNode.right AVLTree.height_node AVLNode.memoized_height AVLNode.height_left_lt_tree AVLNode.height_right_lt_tree)
open BST (AVLNode.mk')

variable (t: AVLNode T) [O: LinearOrder T] (Tcopy: core.marker.Copy T) (H: avl_verification.Ord T)


instance (ty: ScalarTy) : InBounds ty 0 where
  hInBounds := by
    induction ty <;> simp [Scalar.cMax, Scalar.cMin, Scalar.max, Scalar.min] <;> decide

theorem Scalar.zero_le_unsigned {ty} (s: ¬ ty.isSigned) (x: Scalar ty): Scalar.ofInt 0 ≤ x := by
  apply (Scalar.le_equiv _ _).2
  convert x.hmin
  cases ty <;> simp [ScalarTy.isSigned] at s <;> simp [Scalar.min]

@[simp]
theorem Scalar.max_unsigned_left_zero_eq {ty} [s: Fact (¬ ty.isSigned)] (x: Scalar ty):
  Max.max (Scalar.ofInt 0) x = x := max_eq_right (Scalar.zero_le_unsigned s.out x)

@[simp]
theorem Scalar.max_unsigned_right_zero_eq {ty} [s: Fact (¬ ty.isSigned)] (x: Scalar ty):
  Max.max x (Scalar.ofInt 0) = x := max_eq_left (Scalar.zero_le_unsigned s.out x)

@[ext]
theorem Scalar.ext {ty} (a b: Scalar ty): a.val = b.val -> a = b := (Scalar.eq_equiv a b).2

@[pspec]
def max_spec {a b: T}: ∃ o, avl_verification.max _ H Tcopy a b = .ok o ∧ o = O.max a b := by sorry

@[pspec]
def AVLNode.left_height_spec
  (left: AVLNode T): (AVLNode.mk x (some left) right h).left_height = left.height
  := by simp only [AVLNode.left_height]

@[pspec]
def AVLNode.right_height_spec
  (right: AVLNode T): (AVLNode.mk x left (some right) h).right_height = right.height
  := by simp only [AVLNode.right_height]

@[simp, norm_cast]
theorem coe_max {ty: ScalarTy} (a b: Scalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℤ) := by
  -- TODO: there should be a shorter way to prove this.
  rw [max_def, max_def]
  split_ifs <;> simp_all
  refine' absurd _ (lt_irrefl a)
  exact lt_of_le_of_lt (by assumption) ((Scalar.lt_equiv _ _).2 (by assumption))

-- TODO:
@[pspec]
def AVLNode.height_spec (t: AVLNode T): AVLTree.height_node t ≤ Scalar.max .Usize -> ∃ v, t.height = .ok v ∧ v.val = AVLTree.height_node t
  := by
  haveI: Fact (¬ ScalarTy.isSigned .Usize) := ⟨by simp [ScalarTy.isSigned]⟩
  intro Hbound
  simp [AVLNode.height]
  match t with 
  | AVLNode.mk x left right h =>
    rcases Hleft: left with _ | ⟨ a, left_left, left_right, h_left ⟩ <;> rcases Hright: right with _ | ⟨ b, right_left, right_right, h_right ⟩ <;> simp only [AVLNode.left_height,
      AVLNode.right_height, bind_tc_ok, max_self, Nat.cast_add,
      Nat.cast_one]
    -- (none, none) case.
    . progress with max_spec as ⟨ w, Hw ⟩
      simp only [Hw, max_self, AVLTree.height_node_of_mk, Nat.cast_add, Nat.cast_one]
      use 1#usize; norm_cast
    -- (none, some .) case.
    . progress with height_spec as ⟨ w, Hw ⟩
      . push_cast
        refine' le_trans _ Hbound
        apply le_of_lt; rw [Hright]
        exact_mod_cast AVLNode.height_right_lt_tree _
      . progress with max_spec as ⟨ M, Hm ⟩
        rw [Hm]
        have: 1 + w.val ≤ Scalar.max .Usize := by
          rw [Hw]
          refine' le_trans _ Hbound
          conv =>
            rhs
            rw [Hright, AVLTree.height_node, AVLTree.height]
          push_cast
          refine' Int.add_le_add_left _ _
          exact Int.le_max_right _ _
        simp only [Scalar.max_unsigned_left_zero_eq, ge_iff_le, zero_le, max_eq_right, Nat.cast_add,
          Nat.cast_one]
        progress with Usize.add_spec as ⟨ X, Hx ⟩
        simp only [Result.ok.injEq, Nat.cast_add,
          Nat.cast_one, Nat.cast_max, exists_eq_left', Hx, Scalar.ofInt_val_eq, Hw, add_right_inj]
        conv =>
          rhs
          rw [AVLTree.height_node, AVLTree.height, (max_eq_right (zero_le _)), AVLTree.height]
        -- TODO: render invariant by commutativity.
    -- (some ., none) case, above.
    . sorry
    -- (some ., some .) case.
    . progress with height_spec as ⟨ c, Hc ⟩
      -- TODO: factor me out...
      push_cast
      refine' le_trans _ Hbound
      apply le_of_lt; rw [Hleft]
      exact_mod_cast AVLNode.height_left_lt_tree _
      progress with height_spec as ⟨ d, Hd ⟩
      push_cast
      refine' le_trans _ Hbound
      apply le_of_lt; rw [Hright]
      exact_mod_cast AVLNode.height_right_lt_tree _
      progress with max_spec as ⟨ M, Hm ⟩
      have: 1 + M.val ≤ Scalar.max .Usize := by
        rw [Hm]
        refine' le_trans _ Hbound
        rw [Hleft, Hright, AVLTree.height_node, AVLTree.height, AVLTree.height]
        push_cast
        rw [Hc, Hd]
      progress with Usize.add_spec as ⟨ X, Hx ⟩
      simp [Hx, Hm, Hc, Hd, AVLTree.height]
decreasing_by
  all_goals (simp_wf; try simp [Hleft]; try simp [Hright]; try linarith)

-- TODO: discharge all bound requirements
-- by taking (multiple?) hypotheses.
@[pspec]
def AVLNode.update_height_spec (x: T) (h: Usize) (left right: AVLTree T): ∃ t_new, AVLNode.update_height _ (AVLNode.mk x left right h) = .ok t_new ∧ t_new = AVLNode.mk' x left right := by 
  simp [AVLNode.update_height]
  haveI: Fact (¬ ScalarTy.isSigned .Usize) := ⟨by simp [ScalarTy.isSigned]⟩
  rcases Hleft: left with _ | ⟨ a, left_left, left_right, h_left ⟩ <;> rcases Hright: right with _ | ⟨ b, right_left, right_right, h_right ⟩ <;> simp [AVLNode.right_height, AVLNode.left_height]
  -- TODO: clean up proof structure
  -- it's always the same.
  . progress with max_spec as ⟨ w, Hw ⟩
    rw [Hw]; 
    progress as ⟨ H, H_height ⟩
    . simp; scalar_tac
    . simp only [Result.ok.injEq, AVLNode.mk.injEq, true_and]; ext; simp [H_height, AVLTree.height]
  . progress with height_spec as ⟨ c, Hc ⟩
    . sorry
    . progress with max_spec as ⟨ w, Hw ⟩
      simp at Hw; rw [Hw]; progress as ⟨ H, H_height ⟩; simp; sorry -- 1 + c ≤ Usize.max
      simp only [Result.ok.injEq, AVLNode.mk.injEq, true_and]; ext; simp [AVLTree.height, H_height, Hc]
  . progress with height_spec as ⟨ c, Hc ⟩
    . sorry
    . progress with max_spec as ⟨ w, Hw ⟩
      progress as ⟨ H, H_height ⟩
      . sorry
      . simp only [Result.ok.injEq, AVLNode.mk.injEq, true_and]; ext; simp [AVLTree.height, H_height, Hw, Hc]
  . progress with height_spec as ⟨ c, Hc ⟩
    . sorry
    . progress with height_spec as ⟨ d, Hd ⟩
      . sorry
      . progress with max_spec as ⟨ w, Hw ⟩
        progress as ⟨ H, H_height ⟩
        . sorry
        . simp only [Result.ok.injEq, AVLNode.mk.injEq, true_and]; ext; simp [AVLTree.height, H_height, Hw, Hc, Hd]

end Implementation
