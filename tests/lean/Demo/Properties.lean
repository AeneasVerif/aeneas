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

@[pspec]
theorem mul3_add1_spec (x : U32) (h : 3 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul3_add1 x = ret y ∧
  ↑y = 3 * ↑x + (1 : Int)
  := by
  unfold mul3_add1
  progress as ⟨ i ⟩
  progress as ⟨ i1 ⟩
  progress as ⟨ i2 ⟩
  simp; scalar_tac

/-
pub fn use_mul3_add1(x: u32, y: u32) -> u32 {
    mul3_add1(x) + y
}
-/

theorem use_mul3_add1_spec (x : U32) (y : U32)
  (h : 3 * ↑x + 1 + ↑y ≤ U32.max) :
  ∃ z, use_mul3_add1 x y = ret z ∧
  ↑z = 3 * ↑x + (1 : Int) + ↑y := by
  unfold use_mul3_add1
  progress as ⟨ i ⟩
  progress as ⟨ i' ⟩
  simp; scalar_tac

end demo
