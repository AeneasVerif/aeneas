import Aeneas.Std
import Aeneas.Tactic.Step

/-!
# Tests: bind-assoc binder-name preservation

Regression tests for `bindAssocPreservingNames`.  The simproc must preserve
original binder names when `simp` reassociates left-nested `bind` chains.

Each test uses `#guard_msgs` + `trace_state` to verify that names introduced
by `step` / `step*` are the original source-level names (not generic `x✝` etc).
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

/- After `step with`, the name `x` from the inner do-block must be preserved
   (not replaced by a generic name like `x✝` or `a✝`). -/
set_option linter.unusedTactic false in
/--
trace: case a
a : U32
h : ↑a < U32.max - 4
x : U32
hx : ↑x = ↑a + 1
⊢ (do
      let inner ← x + 1#u32
      inner + 2#u32) ⦃
    r => ↑r = ↑a + 4 ⦄
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (a : U32) (h : a.val < U32.max - 4) :
    twoLayer a ⦃ fun r => r.val = a.val + 4 ⦄ := by
  unfold twoLayer
  step with add_one.spec as ⟨x, hx⟩
  trace_state
  sorry

-- Also verify the full proof still works
example (a : U32) (h : a.val < U32.max - 4) :
    twoLayer a ⦃ fun r => r.val = a.val + 4 ⦄ := by
  unfold twoLayer
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

/- After stepping through the chain, all names (i1, z0, z1, o) are preserved. -/
set_option linter.unusedTactic false in
/--
trace: case a
a : U32
h : ↑a < 50
i1 : U32
hi1 : ↑i1 = ↑a + 1
z0 : U32
z0_post : ↑z0 = ↑i1 + 2
z1 : U32
z1_post : ↑z1 = ↑i1 + 3
o : U32
o_post : ↑o = ↑z0 + ↑z1
⊢ z1 + o ⦃ r => ↑r < 500 ⦄
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (a : U32) (h : a.val < 50) :
    main_fn a ⦃ fun r => r.val < 500 ⦄ := by
  unfold main_fn prefix_fn
  step with add_one.spec as ⟨i1, hi1⟩
  step as ⟨z0, z0_post⟩
  step as ⟨z1, z1_post⟩
  step as ⟨o, o_post⟩
  trace_state
  sorry

-- Also verify the full proof still works
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

/- After `step*`, every variable has its original source-level name
   (i1, z0, z1, o, r) — not inaccessible names like `x✝`. -/
set_option linter.unusedTactic false in
/--
trace: a : U32
h : ↑a < 50
i1 : U32
_✝³ : [> let i1 ← add_one a <]
i1_post : ↑i1 = ↑a + 1
z0 : U32
_✝² : [> let z0 ← i1 + 2#u32 <]
z0_post : ↑z0 = ↑i1 + 2
z1 : U32
_✝¹ : [> let z1 ← i1 + 3#u32 <]
z1_post : ↑z1 = ↑i1 + 3
o : U32
_✝ : [> let o ← z0 + z1 <]
o_post : ↑o = ↑z0 + ↑z1
r : U32
_ : [> let r ← z1 + o <]
r_post : ↑r = ↑z1 + ↑o
⊢ ↑r = 2 * ↑a + 9
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (a : U32) (h : a.val < 50) :
    main_fn a ⦃ fun r => r.val = 2 * a.val + 9 ⦄ := by
  unfold main_fn prefix_fn
  step*
  trace_state
  sorry

-- Also verify that step* can close the goal with a simpler postcondition
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
