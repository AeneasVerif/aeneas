import Avl.Tree
import Avl.Spec
import Avl.OrderSpec
import Avl.ScalarOrder

open Primitives

namespace avl

----variable (t: AVLNode T) [O: LinearOrder T] (Tcopy: core.marker.Copy T) (H: avl.Ord T)

-- TODO: remove?
theorem Scalar.zero_le_unsigned {ty} (s: ¬ ty.isSigned) (h : Scalar.cMin ty ≤ 0 ∧ 0 ≤ Scalar.cMax ty)
  (x: Scalar ty) : Scalar.ofInt 0 h ≤ x := by
  apply (Scalar.le_equiv _ _).2
  convert x.hmin
  cases ty <;> simp [ScalarTy.isSigned] at s <;> simp [Scalar.min]

@[simp]
theorem Scalar.max_unsigned_left_zero_eq {ty} [s: Fact (¬ ty.isSigned)]
  (h : Scalar.cMin ty ≤ 0 ∧ 0 ≤ Scalar.cMax ty) (x: Scalar ty):
  Max.max (Scalar.ofInt 0 h) x = x := max_eq_right (Scalar.zero_le_unsigned s.out h x)

@[simp]
theorem Scalar.max_unsigned_right_zero_eq {ty} [s: Fact (¬ ty.isSigned)]
  (h : Scalar.cMin ty ≤ 0 ∧ 0 ≤ Scalar.cMax ty) (x: Scalar ty):
  Max.max x (Scalar.ofInt 0 h) = x := max_eq_left (Scalar.zero_le_unsigned s.out h x)

@[ext]
theorem Scalar.ext {ty} (a b: Scalar ty): a.val = b.val -> a = b := (Scalar.eq_equiv a b).2

@[pspec]
def max_spec (ordInst : avl.Ord T) (instCopy : core.marker.Copy T)
  [O: LinearOrder T] [ordSpecInst : OrdSpecLinearOrderEq ordInst] (a b : T) :
  ∃ o, avl.get_max _ ordInst instCopy a b = .ok o ∧ o = O.max a b := by
  rw [get_max]
  have Hcmp := ordSpecInst.infallible
  progress as ⟨ o, Hpost ⟩; clear Hcmp
  split <;> simp_all [O.compare_eq_compareOfLessAndEq, compareOfLessAndEq, max_def] <;>
  cases h: a == b <;> simp_all <;> split <;> simp_all
  . simp only [O.lt_iff_le_not_le] at *
    tauto
  . -- TODO: cases doesn't work here
    if h : a < b then simp_all
    else simp_all
  . have := O.le_antisymm a b
    simp_all

@[simp, norm_cast]
theorem coe_max {ty: ScalarTy} (a b: Scalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℤ) := by
  -- TODO: there should be a shorter way to prove this.
  rw [max_def, max_def]
  split_ifs <;> simp_all

@[pspec]
def Node.left_height_spec [LinearOrder T] (node : Node T) (hInv : Child.inv node.left):
  ∃ h, Node.left_height _ node = .ok h ∧
  h.val = Child.compute_height node.left := by
  rw [left_height]
  match h: node.left with
  | none => simp [*]
  | some child =>
    simp [h] at hInv
    have := Node.inv_imp_height_eq hInv
    simp [*]

@[pspec]
def Node.right_height_spec [LinearOrder T] (node : Node T) (hInv : Child.inv node.right):
  ∃ h, Node.right_height _ node = .ok h ∧
  h.val = Child.compute_height node.right := by
  rw [right_height]
  match h: node.right with
  | none => simp [*]
  | some child =>
    simp [h] at hInv
    have := Node.inv_imp_height_eq hInv
    simp [*]

@[pspec]
def Node.update_height_spec {T : Type} [LinearOrder T]
  (node : Node T) (h : node.compute_height ≤ Usize.max)
  (hLeftInv : Child.inv node.left) (hRightInv : Child.inv node.right) :
  ∃ node', Node.update_height _ node = .ok node' ∧
  node'.left = node.left ∧
  node'.right = node.right ∧
  node'.value = node.value ∧
  node'.height.val = node.compute_height := by
  rw [update_height]
  progress as ⟨ hLeft .. ⟩
  progress as ⟨ hRight .. ⟩
  progress as ⟨ hMax .. ⟩
  have h : 1 + hMax.val ≤ Usize.max := by
    cases node; simp_all
  progress as ⟨ height .. ⟩
  simp
  cases node; simp_all

end avl
