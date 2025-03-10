import Aeneas
import Demo.Demo
open Aeneas.Std
open Result

namespace demo

#check U32.add_spec

-- @[progress]
theorem mul2_add1_spec (x : U32) (h : 2 * x + 1 ≤ (U32.max : Int))
  : ∃ y, mul2_add1 x = ok y ∧
  ↑y = 2 * ↑x + (1 : Int)
  := by
  rw [mul2_add1]
  progress with U32.add_spec as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

theorem use_mul2_add1_spec (x : U32) (y : U32) (h : 2 * x + 1 + y ≤ (U32.max : Nat)) :
  ∃ z, use_mul2_add1 x y = ok z ∧
  ↑z = 2 * ↑x + (1 : Nat) + ↑y := by
  rw [use_mul2_add1]
  progress with mul2_add1_spec as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

open CList

@[simp] def CList.toList {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.toList

theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  ∃ x, list_nth l i = ok x ∧
  x = l.toList[i.val]!
  := by
  rw [list_nth]
  match l with
  | CNil =>
    simp_all
  | CCons hd tl =>
    simp_all
    if hi: i = 0#u32 then
      simp_all
    else
      simp_all
      progress as ⟨ i1 ⟩
      progress as ⟨ x ⟩
      simp_all

theorem i32_id_spec (n : I32) (h : 0 ≤ n.val) :
  i32_id n = ok n := by
  rw [i32_id]
  split
  . simp [*]
  . progress as ⟨ n1 ⟩
    progress
    progress as ⟨ n2 ⟩
    scalar_tac
termination_by n.toNat
decreasing_by simp_wf; scalar_tac

theorem list_tail_spec {T : Type} [Inhabited T] (l : CList T) :
  ∃ back, list_tail l = ok (CList.CNil, back) ∧
  ∀ tl', ∃ l', back tl' = l' ∧ l'.toList = l.toList ++ tl'.toList := by
  rw [list_tail]
  match l with
  | CNil =>
    simp_all
  | CCons hd tl =>
    simp_all
    progress as ⟨ back ⟩
    simp
    -- Proving the backward function
    intro tl'
    simp_all

end demo
