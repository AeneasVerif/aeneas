module
public import Aeneas.Tactic.Solver.ScalarTac.Lemmas
public section

/-!
# `grind` pattern-selection tests for the Aeneas `.val` projections
-/

namespace Aeneas.Grind.Tests

open Aeneas Std

/-!
## Regression test — `.val` must not be used as an e-match pattern head, as it
leads to extremely inefficient patterns. The fix is to mark `UScalar.val` with
`grind symbol low`. If we don't do so, we get a maxHeartbeats error in the
following test.
-/
namespace GrindValPatternBlowup

private opaque MBuf : Type
private def blen : MBuf → Nat := fun _ => 100
private def wlen : MBuf → Nat := fun _ => 200

/-- A global `@[grind]` lemma the goal is closed through — this forces `grind`
    into the e-match loop (so the pathological trigger is actually exercised)
    while keeping the goal provable both with and without the fix. -/
@[grind =]
private theorem wlen_eq (b : MBuf) : wlen b = blen b + 100 := by
  simp [blen, wlen]

/-- Distinctive default-priority application covering all 12 scalar variables
    (mirrors the recursive `loop0` / `vloop0` call in the real proof). -/
private opaque Cov : MBuf → Usize → Usize → Usize → Usize → Usize → Usize → Usize →
  Usize → Usize → Usize → Usize → Usize → Prop

/-- Induction-hypothesis analog: every variable appears as a lone `xᵢ.val ≤ kᵢ`
    premise (distinct bounds), plus the single covering application `Cov …`. -/
private abbrev IH : Prop :=
  ∀ (b : MBuf) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Usize),
    x1.val ≤ 1 → x2.val ≤ 2 → x3.val ≤ 3 → x4.val ≤ 4 → x5.val ≤ 5 → x6.val ≤ 6 →
    x7.val ≤ 7 → x8.val ≤ 8 → x9.val ≤ 9 → x10.val ≤ 10 → x11.val ≤ 11 → x12.val ≤ 12 →
    Cov b x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12

set_option maxHeartbeats 200000 in
example (b : MBuf) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Usize)
    -- 12 extra in-scope scalar `.val` terms, to inflate the combinatorial cost of
    -- matching the (unfixed) raw multi-`.val` trigger:
    (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 : Usize)
    (_ih : IH) (_hcov : Cov b x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (_g1 : y1.val ≤ 101) (_g2 : y2.val ≤ 102) (_g3 : y3.val ≤ 103) (_g4 : y4.val ≤ 104)
    (_g5 : y5.val ≤ 105) (_g6 : y6.val ≤ 106) (_g7 : y7.val ≤ 107) (_g8 : y8.val ≤ 108)
    (_g9 : y9.val ≤ 109) (_g10 : y10.val ≤ 110) (_g11 : y11.val ≤ 111) (_g12 : y12.val ≤ 112)
    (_h1 : x1.val ≤ 1) (_h2 : x2.val ≤ 2) (_h3 : x3.val ≤ 3) (_h4 : x4.val ≤ 4)
    (_h5 : x5.val ≤ 5) (_h6 : x6.val ≤ 6) (_h7 : x7.val ≤ 7) (_h8 : x8.val ≤ 8)
    (_h9 : x9.val ≤ 9) (_h10 : x10.val ≤ 10) (_h11 : x11.val ≤ 11) (_h12 : x12.val ≤ 12)
    (_hb : blen b = 5000) :
    blen b < wlen b := by
  grind

end GrindValPatternBlowup

end Aeneas.Grind.Tests
