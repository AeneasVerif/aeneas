module
public import Aeneas.Std.Core.Iter
public import Aeneas.Tactic.Step.Init
public section

namespace Aeneas.Std

open Result

/-- An inhabited `usize` range yields its start and advances by one without overflow. -/
theorem core.iter.range.IteratorRange.next_usize_some
    (start stop : Usize) (h : start.val < stop.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := start, «end» := stop }
      = ok (some start,
          { start := Usize.ofNatCore (start.val + 1) (by scalar_tac), «end» := stop }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked, core.cmp.impls.PartialOrdUsize.lt,
    h, show start.val < UScalar.max .Usize from by scalar_tac]
  rfl

/-- Empty and reversed `usize` ranges are exhausted and remain unchanged. -/
theorem core.iter.range.IteratorRange.next_usize_none
    (start stop : Usize) (h : ¬ start.val < stop.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := start, «end» := stop }
      = ok (none, { start := start, «end» := stop }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt, h]

/-- Deterministic, total specification for `Range<usize>::next`, used by `step`. -/
@[step]
theorem core.iter.range.IteratorRange.next_usize_spec
    (r : core.ops.range.Range Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      ⦃ item r' =>
        if r.start.val < r.«end».val then
          item = some r.start ∧ r'.start.val = r.start.val + 1 ∧ r'.«end» = r.«end»
        else item = none ∧ r' = r ⦄ := by
  rcases r with ⟨start, stop⟩
  by_cases h : start.val < stop.val
  · rw [core.iter.range.IteratorRange.next_usize_some start stop h]
    simp only [WP.spec_ok, h, ite_true]
    exact ⟨rfl, rfl, rfl⟩
  · rw [core.iter.range.IteratorRange.next_usize_none start stop h]
    simp only [WP.spec_ok, h, ite_false]
    exact ⟨rfl, rfl⟩

end Aeneas.Std
