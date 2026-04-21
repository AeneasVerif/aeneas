import Aeneas
import Demo.Demo
open Aeneas Std Result

#setup_aeneas_simps

namespace demo

-- @[step]
theorem mul2_add1.spec (x : U32) (h : 2 * x.toNat + 1 ≤ U32.max)
  : mul2_add1 x ⦃ y => y.toNat = 2 * x.toNat + (1 : Nat) ⦄
  := by
  unfold mul2_add1
  step as ⟨ i ⟩
  step as ⟨ i' ⟩
  scalar_tac

theorem use_mul2_add.spec (x : U32) (y : U32) (h : 2 * x.toNat + 1 + y.toNat ≤ U32.max) :
  use_mul2_add1 x y ⦃ z => ↑z = 2 * ↑x + (1 : Nat) + ↑y ⦄ := by
  unfold use_mul2_add1
  step with mul2_add1.spec as ⟨ i ⟩
  step as ⟨ i' ⟩
  scalar_tac

theorem mod_add.spec (x y : U32) (h : x.toNat < 3329 ∧ y.toNat < 3329) :
  mod_add x y ⦃ z => z.toNat = (x.toNat + y.toNat) % 3329 ⦄ := by
  unfold mod_add
  step*
  toBitVec_tac 32

open CList

@[simp, grind] def CList.toList {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.toList

theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.toNat < l.toList.length) :
  list_nth l i ⦃ x => x = l.toList[i.toNat]! ⦄
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
      step as ⟨ i1 ⟩
      step as ⟨ x ⟩
      simp_lists [*]

theorem i32_id_spec (n : I32) (h : 0 ≤ n.toInt) :
  i32_id n ⦃ n' => n' = n ⦄ := by
  unfold i32_id
  split
  . simp [*]
  . step as ⟨ n1 ⟩
    step
    step as ⟨ n2 ⟩
    scalar_tac
termination_by n.toNat
decreasing_by simp_wf; scalar_tac

theorem list_tail_spec {T : Type} [Inhabited T] (l : CList T) :
  list_tail l ⦃ tl back =>
    tl = CList.CNil ∧
    ∀ tl', let l' := back tl'; l'.toList = l.toList ++ tl'.toList ⦄ := by
  unfold list_tail
  match l with
  | CNil => simp
  | CCons hd tl =>
    step as ⟨ back ⟩
    grind

end demo
