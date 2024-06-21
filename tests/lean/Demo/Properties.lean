import Base
import Demo.Demo
open Primitives
open Result

namespace demo

#check U32.add_spec

example (a: Slice U32) (u: U32):
  a.val = [u] →
  a.length = 1#usize := by
  intro h
  simp [h, Slice.len, Usize.ofInt, Usize.ofIntCore]

example (a: Slice U32) (u: U32):
  a.val = [u] →
  a.val.len = 1 := by
  intro h
  simp [h]

#check Scalar.eq_equiv

example (a: Slice U32) (u: U32):
  a.val = [u] →
  a.length = 1#usize := by
  intro h
  simp [h]

@[simp] theorem Scalar.eq_imp {x y : U32} (h : x.val = y.val) :
  x = y := sorry

example (f : U32 → Bool) (x : U32) (y : U32) (h : x.val = y.val) : f x := by
  have := Scalar.eq_imp h
  simp [Scalar.eq_imp h]


theorem use_mul2_add1_spec (x : U32) (y : U32) (h : 2 * ↑x + 1 + ↑y ≤ U32.max) :
  ∃ z, use_mul2_add1 x y = ok z ∧
  ↑z = 2 * ↑x + (1 : Int) + ↑y := by
  rw [use_mul2_add1]
  progress with mul2_add1_spec as ⟨ i ⟩
  progress as ⟨ i' ⟩
  simp; scalar_tac

open CList

@[simp] def CList.to_list {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.to_list

theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : ↑i < l.to_list.len) :
  ∃ x, list_nth T l i = ok x ∧
  x = l.to_list.index ↑i
  := by
  rw [list_nth]
  match l with
  | CNil =>
    simp_all; scalar_tac
  | CCons hd tl =>
    simp_all
    if hi: i = 0#u32 then
      simp_all
    else
      simp_all
      progress as ⟨ i1 ⟩
      progress as ⟨ x ⟩
      simp_all

theorem i32_id_spec (x : I32) (h : 0 ≤ x.val) :
  ∃ y, i32_id x = ok y ∧ x.val = y.val := by
  rw [i32_id]
  if hx : x = 0#i32 then
    simp_all
  else
    simp_all
    progress as ⟨ x1 ⟩
    progress as ⟨ x2 ⟩
    progress
    simp_all
termination_by x.val.toNat
decreasing_by scalar_decr_tac

theorem list_tail_spec {T : Type} [Inhabited T] (l : CList T) :
  ∃ back, list_tail T l = ok (CList.CNil, back) ∧
  ∀ tl', ∃ l', back tl' = ok l' ∧ l'.to_list = l.to_list ++ tl'.to_list := by
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
    progress
    simp_all

end demo
