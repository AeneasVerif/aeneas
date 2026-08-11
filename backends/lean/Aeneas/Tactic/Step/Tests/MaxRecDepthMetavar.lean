import Aeneas.Do
import Aeneas.Std.Slice
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

/-!
# Regression test — `step*` and metavariable preconditions that triggered
a maximum recursion depth.
-/

namespace StepMaxRecDepthMetavar

/-- Vector-of-bits hash, mirroring `Spec.SHA2.Hash .sha512`. -/
private abbrev MyHash := Vector (Vector Bool 64) 8

/-- WHNF-heavy `Array U64 → MyHash` conversion, mirroring `hashToSpec512`. -/
private def conv (h : Array U64 8#usize) : MyHash :=
  Vector.ofFn fun (i : Fin 8) =>
    Vector.ofFn fun (k : Fin 64) => (h.val[i.val]!).bv.getMsbD k.val

/-- Structured `Prop` precondition, mirroring `appendPartial512`. -/
private def convEq (h : Array U64 8#usize) (iv : MyHash) : Prop := conv h = iv

/-- Trivial monadic function to `step` over (mirrors `append_bulk`). -/
private def myFn (h : Array U64 8#usize) : Result (Array U64 8#usize) := ok h

/-- The helper's precondition `convEq h iv` has `iv` undetermined by the
    call argument `h`, so `step` turns it into a metavariable. -/
@[local step]
private theorem myFn_spec (h : Array U64 8#usize) (iv : MyHash) (hp : convEq h iv) :
    myFn h ⦃ (r : Array U64 8#usize) => convEq r iv ⦄ := by
  unfold myFn; step*

/- Two binds: the second `step` dispatches `myFn_spec` over the opaque
   intermediate `h1`, discharging `convEq h1 ?iv`.  This used to recurse to
   `maximum recursion depth`; it must now succeed. -/
set_option maxRecDepth 512 in
private theorem two_binds (h : Array U64 8#usize) (iv : MyHash) (hp : convEq h iv) :
    (do let h1 ← myFn h
        let h2 ← myFn h1
        ok h2) ⦃ (r : Array U64 8#usize) => convEq r iv ⦄ := by
  step*

end StepMaxRecDepthMetavar
