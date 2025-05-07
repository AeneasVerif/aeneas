import Aeneas
import Demo.Demo
open Aeneas.Std
open Result

#setup_aeneas_simps

namespace demo

-- @[progress]
theorem mul2_add1.spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max)
  : ∃ y, mul2_add1 x = ok y ∧
  y.val = 2 * x.val + (1 : Nat)
  := by
  unfold mul2_add1
  progress as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

theorem use_mul2_add.spec (x : U32) (y : U32) (h : 2 * x.val + 1 + y.val ≤ U32.max) :
  ∃ z, use_mul2_add1 x y = ok z ∧
  ↑z = 2 * ↑x + (1 : Nat) + ↑y := by
  unfold use_mul2_add1
  progress with mul2_add1.spec as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

theorem mod_add.spec (x y : U32) (h : x.val < 3329 ∧ y.val < 3329) :
  ∃ z, mod_add x y = ok z ∧ z.val = (x.val + y.val) % 3329 := by
  unfold mod_add
  progress*
  bv_tac 32

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
  unfold list_nth
  match l with
  | CNil =>
    simp_all
  | CCons hd tl =>
    simp_all
    if hi: i = 0#u32 then
      simp [*]
    else
      simp [*]
      progress as ⟨ i1 ⟩
      progress as ⟨ x ⟩
      simp_lists [*]

theorem i32_id_spec (n : I32) (h : 0 ≤ n.val) :
  i32_id n = ok n := by
  unfold i32_id
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
  unfold list_tail
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
