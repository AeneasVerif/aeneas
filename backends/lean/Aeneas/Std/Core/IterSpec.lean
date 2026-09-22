/- Specs for the `core::iter` iterators.

   The iterator `next` functions (Core/Iter.lean) are extracted as plain `def`s
   with no reasoning lemmas, so `progress` / `let*` cannot step through a
   `for i in a..b` loop: every downstream project re-derives a `next` lemma by
   hand. This file provides the missing `@[step]` spec for the `usize` range
   iterator, the overwhelmingly common case. -/
import Aeneas.Std.Core.Iter
import Aeneas.Tactic.Step.Init

namespace Aeneas.Std

open Result Error WP

/-- **Spec for the `usize` range iterator's `next`** (the engine of
    `for i in a..b`): while `start < end` it yields `start` and advances the range
    by one; otherwise it reports exhaustion, leaving the range unchanged.

    Registered `@[step]` so `progress` / `let*` step straight through range-`for`
    loops. The result is deterministic, so a single spec with an `if` postcondition
    suffices; callers `split` on `start < end`. -/
@[step]
theorem core.iter.range.IteratorRange.next_StepUsize_spec
    (r : core.ops.range.Range Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      ⦃ res =>
        if r.start.val < r.«end».val then
          res.1 = some r.start ∧ res.2.start.val = r.start.val + 1 ∧ res.2.«end» = r.«end»
        else res.1 = none ∧ res.2 = r ⦄ := by
  by_cases h : r.start.val < r.«end».val
  · have hcmp : core.iter.range.StepUsize.partialOrdInst.lt r.start r.«end» = ok true := by
      show liftFun2 core.cmp.impls.PartialOrdUsize.lt r.start r.«end» = ok true
      simp [liftFun2, core.cmp.impls.PartialOrdUsize.lt, h]
    have hck := core.num.checked_add_UScalar_bv_spec r.start 1#usize
    have h1 : (1#usize).val = 1 := rfl
    cases hopt : core.num.checked_add_UScalar r.start 1#usize
    · -- overflow ⇒ impossible: `r.start < r.end ≤ usize::MAX`
      rw [hopt] at hck
      exfalso
      rw [h1] at hck
      scalar_tac
    · -- `r.start + 1` is in range
      rename_i w
      rw [hopt] at hck
      have heval : core.iter.range.IteratorRange.next core.iter.range.StepUsize r
          = ok (some r.start, { r with start := w }) := by
        unfold core.iter.range.IteratorRange.next
        rw [hcmp]
        simp only [bind_tc_ok, reduceIte, liftFun1, core.clone.impls.CloneUsize.clone]
        unfold core.iter.range.StepUsize.forward_checked
        simp only [Usize.checked_add, hopt, bind_tc_ok]
      rw [heval, WP.spec_ok, if_pos h]
      exact ⟨rfl, by rw [hck.2.1, h1], rfl⟩
  · have hcmp : core.iter.range.StepUsize.partialOrdInst.lt r.start r.«end» = ok false := by
      show liftFun2 core.cmp.impls.PartialOrdUsize.lt r.start r.«end» = ok false
      simp [liftFun2, core.cmp.impls.PartialOrdUsize.lt, h]
    have heval : core.iter.range.IteratorRange.next core.iter.range.StepUsize r = ok (none, r) := by
      unfold core.iter.range.IteratorRange.next
      rw [hcmp]
      simp only [bind_tc_ok, Bool.false_eq_true, reduceIte]
    rw [heval, WP.spec_ok, if_neg h]
    exact ⟨rfl, rfl⟩

end Aeneas.Std
