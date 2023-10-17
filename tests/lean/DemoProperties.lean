import Base
import Demo
open Primitives
open Result

namespace demo

#check U32.add_spec

@[pspec] -- registers the theorem
theorem mul2_add1_spec (x : U32) (h : 2 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul2_add1 x = ret y ∧
  ↑y = 2 * ↑x + (1 : Int)
  := by
  rw [mul2_add1]
  progress as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

theorem use_mul2_add1_spec (x : U32) (y : U32) (h : 2 * ↑x + 1 + ↑y ≤ U32.max) :
  ∃ z, use_mul2_add1 x y = ret z ∧
  ↑z = 2 * ↑x + (1 : Int) + ↑y := by
  rw [use_mul2_add1]
  progress as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

open CList

@[simp] def CList.to_list {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.to_list

theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : ↑i < l.to_list.len) :
  ∃ x, list_nth T l i = ret x ∧
  x = l.to_list.index ↑i
  := by
  rw [list_nth]
  match l with
  | CNil =>
    scalar_tac
  | CCons hd tl =>
    simp_all
    if hi: i = 0#u32 then
      simp_all
    else
      simp_all
      progress as ⟨ i1 ⟩
      progress as ⟨ l1 ⟩
      simp_all

theorem i32_id_spec (x : I32) (h : 0 ≤ x.val) :
  ∃ y, i32_id x = ret y ∧ x.val = y.val := by
  rw [i32_id]
  if hx : x = 0#i32 then
    simp_all
  else
    simp_all
    progress as ⟨ x1 ⟩
    progress as ⟨ x2 ⟩
    progress
    simp; scalar_tac
termination_by i32_id_spec x _ => x.val.toNat
decreasing_by scalar_decr_tac

end demo
