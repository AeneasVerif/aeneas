import Aeneas.Std
import Aeneas.Tactic.Step

/-!
# Tests: bind-assoc binder-name preservation

Regression tests for `bindAssocPreservingNames`.  The simproc must preserve
original binder names when `simp` reassociates left-nested `bind` chains.
-/

namespace Aeneas.Step.Test.BindAssocNames

open Aeneas Std Result

-- ============================================================
-- Helpers
-- ============================================================

private def add_one (a : U32) : Result U32 := a + 1#u32

@[step]
private theorem add_one.spec (a : U32) (h : a.val < U32.max) :
    add_one a ⦃ fun r => r.val = a.val + 1 ⦄ := by
  unfold add_one; step; grind

-- ============================================================
-- 1. Single left-nesting (2 layers)
-- ============================================================

/-- Two-layer nesting: `do let r ← (do let x ← f; g x); h r`.
    After inlining + bind-assoc, the name `x` should survive. -/
private def twoLayer (a : U32) : Result U32 := do
  let inner ← (do let x ← add_one a; x + 1#u32)
  inner + 2#u32

example (a : U32) (h : a.val < U32.max - 4) :
    twoLayer a ⦃ fun r => r.val = a.val + 4 ⦄ := by
  unfold twoLayer
  -- After `step with`, the continuation should mention `x`, not a generic name.
  step with add_one.spec as ⟨x, hx⟩
  step as ⟨inner, hinner⟩
  step
  grind

-- ============================================================
-- 2. Deep nesting (4 layers)
-- ============================================================

private def prefix_fn (a : U32) : Result (U32 × U32 × U32) := do
  let i1 ← add_one a
  let z0 ← i1 + 2#u32
  let z1 ← i1 + 3#u32
  let o  ← z0 + z1
  .ok (i1, z1, o)

private def main_fn (a : U32) : Result U32 := do
  let (_i1, z1, o) ← prefix_fn a
  z1 + o

/-- `step with` + repeated `step` must keep z0, z1, o (not x / x_1 / x✝). -/
example (a : U32) (h : a.val < 50) :
    main_fn a ⦃ fun r => r.val < 500 ⦄ := by
  unfold main_fn prefix_fn
  step with add_one.spec as ⟨i1, hi1⟩
  step as ⟨z0, z0_post⟩
  step as ⟨z1, z1_post⟩
  step as ⟨o, o_post⟩
  step
  grind

-- ============================================================
-- 3. step* preserves names (no inaccessible ✝)
-- ============================================================

/-- After `step*`, every hypothesis should have a user-provided or
    compiler-chosen name — no `✝` suffixes. -/
example (a : U32) (h : a.val < 50) :
    main_fn a ⦃ fun r => r.val < 500 ⦄ := by
  unfold main_fn prefix_fn
  step*

-- ============================================================
-- 4. Plain nested do-blocks (no step with)
-- ============================================================

/-- Nested `do` blocks handled by plain `step`. -/
example {α : Type} (v : alloc.vec.Vec α) (i : Usize) (x : α)
    (hbounds : i.val < v.length) :
    (do
      (do
        let _ ← v.update i x
        .ok ())
      .ok ()) ⦃ _ => True ⦄ := by
  step

end Aeneas.Step.Test.BindAssocNames
