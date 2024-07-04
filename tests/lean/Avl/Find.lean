import Avl.Spec
import Avl.OrderSpec

open Primitives Result

namespace avl

@[pspec]
theorem Tree.find_loop_spec
  {T : Type} (OrdInst : Ord T)
  [DecidableEq T] [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (value : T) (t : Child T) (hInv : Child.inv t) :
  ∃ b, Tree.find_loop T OrdInst value t = ok b ∧
  (b ↔ value ∈ Child.v t) := by
  rewrite [find_loop]
  match t with
  | none => simp
  | some (.mk v left right height) =>
    dsimp only
    have hCmp := Ospec.infallible
    progress keep Hordering as ⟨ ordering ⟩; clear hCmp
    have hInvLeft := Node.inv_left hInv
    have hInvRight := Node.inv_right hInv
    cases ordering <;> dsimp only
    . /- node.value < value -/
      progress
      have hNotIn := Node.lt_imp_not_in_left _ hInv
      simp_all
      intro; simp_all
    . /- node.value = value -/
      simp_all
    . /- node.value > value -/
      progress
      have hNotIn := Node.lt_imp_not_in_right _ hInv
      simp_all
      intro; simp_all

theorem Tree.find_spec
  {T : Type} (OrdInst : Ord T)
  [DecidableEq T] [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (t : Tree T) (value : T) (hInv : t.inv) :
  ∃ b, Tree.find T OrdInst t value = ok b ∧
  (b ↔ value ∈ t.v) := by
  rw [find]
  progress
  simp [Tree.v]; assumption

end avl
