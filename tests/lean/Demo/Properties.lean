import Aeneas
import Demo.Demo
open Aeneas.Std
open Result WP

#setup_aeneas_simps

namespace demo

-- @[progress]
theorem mul2_add1.spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max)
  : mul2_add1 x ⦃ y => y.val = 2 * x.val + (1 : Nat) ⦄
  := by
  unfold mul2_add1
  progress as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

theorem use_mul2_add.spec (x : U32) (y : U32) (h : 2 * x.val + 1 + y.val ≤ U32.max) :
  use_mul2_add1 x y ⦃ z => ↑z = 2 * ↑x + (1 : Nat) + ↑y ⦄ := by
  unfold use_mul2_add1
  progress with mul2_add1.spec as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

theorem mod_add.spec (x y : U32) (h : x.val < 3329 ∧ y.val < 3329) :
  mod_add x y ⦃ z => z.val = (x.val + y.val) % 3329 ⦄ := by
  unfold mod_add
  progress*
  bv_tac 32

open CList

@[simp, grind] def CList.toList {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.toList

theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  list_nth l i ⦃ x => x = l.toList[i.val]! ⦄
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
  i32_id n ⦃ n' => n' = n ⦄ := by
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
  list_tail l ⦃ (tl, back) =>
    tl = CList.CNil ∧
    ∀ tl', let l' := back tl'; l'.toList = l.toList ++ tl'.toList ⦄ := by
  unfold list_tail
  match l with
  | CNil => grind
  | CCons hd tl =>
    progress as ⟨ back ⟩
    grind

end demo
