module
public import Aeneas
public import Arc.Arc
public section

open Aeneas Aeneas.Std Result

/-! Specifications of the examples of the model of `Arc`: the content is shared and immutable. -/

namespace arc

theorem new_five_spec : new_five ⦃ r => r = 5#u32 ⦄ := by
  unfold new_five
  step*

theorem clone_five_spec : clone_five ⦃ r => r = (5#u32, 5#u32) ⦄ := by
  unfold clone_five
  step*

theorem from_x_spec (x : U32) : from_x x ⦃ b => b = true ⦄ := by
  unfold from_x
  step*

theorem as_ref_and_borrow_spec (x : U32) : as_ref_and_borrow x ⦃ r => r = (x, x) ⦄ := by
  unfold as_ref_and_borrow
  step*

@[step]
theorem apply_spec (cfg : alloc.sync.Arc Config) (x : U32)
    (h : x.val * cfg.val.scale.val + cfg.val.offset.val ≤ U32.max) :
    apply cfg x ⦃ r => r.val = x.val * cfg.val.scale.val + cfg.val.offset.val ⦄ := by
  unfold apply
  step*

/-- The clone sees the same content as the original: both applications use the same `Config`. -/
theorem share_spec (cfg : alloc.sync.Arc Config) (x y : U32)
    (hx : x.val * cfg.val.scale.val + cfg.val.offset.val ≤ U32.max)
    (hy : y.val * cfg.val.scale.val + cfg.val.offset.val ≤ U32.max) :
    share cfg x y ⦃ r =>
      r.1.val = x.val * cfg.val.scale.val + cfg.val.offset.val ∧
      r.2.val = y.val * cfg.val.scale.val + cfg.val.offset.val ⦄ := by
  unfold share
  step*

end arc
