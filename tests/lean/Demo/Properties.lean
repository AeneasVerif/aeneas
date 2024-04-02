import Base
import Demo.Demo
open Primitives
open Result

namespace demo

/-
pub fn mul3_add1(x: u32) -> u32 {
    x + x + x + 1
}
-/

-- @[pspec]
theorem mul3_add1_spec (x : U32) (h : 3 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul3_add1 x = ret y ∧
  ↑y = 3 * ↑x + (1 : Int)
  := by
  rw [mul3_add1]
  progress as ⟨ i ⟩
  progress as ⟨ i1 ⟩
  progress as ⟨ i2 ⟩
  simp; scalar_tac

/-
pub fn use_mul3_add1(x: u32, y: u32) -> u32 {
    mul3_add1(x) + y
}
-/

theorem use_mul3_add1_spec (x : U32) (y : U32) (h : 3 * ↑x + 1 + ↑y ≤ U32.max) :
  ∃ z, use_mul3_add1 x y = ret z ∧
  ↑z = 3 * ↑x + (1 : Int) + ↑y := by
  rw [use_mul3_add1]
  progress with mul3_add1_spec as ⟨ i ⟩
  progress as ⟨ i' ⟩
  simp; scalar_tac

/-
pub fn use_counter<'a, T: Counter>(cnt: &'a mut T) -> usize {
    let _ = cnt.incr();
    cnt.incr()
}
-/

theorem use_counter_spec {T : Type} (counterInst : Counter T) (cnt : T)
  /- Specifying Counter -/
  (to_int : T → Int)
  (incrSpec :
    ∀ cnt,
      to_int cnt < Usize.max →
      ∃ v cnt',
        counterInst.incr cnt = ret (v, cnt') ∧
        to_int cnt = v ∧ to_int cnt' = to_int cnt + 1)
  /- -/
  (h : to_int cnt < Usize.max - 1) :
  ∃ v cnt', use_counter T counterInst cnt = ret (v, cnt') := by
  rw [use_counter]
  progress
  progress
  simp

theorem use_counter_spec1 {T : Type} (counterInst : Counter T) (cnt : T)
  /- Specifying Counter -/
  (incrSpec :
    ∀ cnt,
      ∃ v cnt',
        counterInst.incr cnt = ret (v, cnt'))
  /- -/ :
  ∃ v cnt', use_counter T counterInst cnt = ret (v, cnt') := by
  rw [use_counter]
  progress
  progress
  simp

/-
pub fn use_vec_index(i: usize, v: &Vec<u32>) -> u32 {
    *(v.index(i))
}
-/

def use_vec_index_spec (i : Usize) (v : alloc.vec.Vec U32) (h : i < v.len) :
  ∃ x, use_vec_index i v = ret x := by
  rw [use_vec_index]
  simp
  progress
  simp

end demo
