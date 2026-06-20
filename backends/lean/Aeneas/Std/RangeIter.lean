/- Step specs for Range/StepBy iterators on Usize.
   These use WP.spec_bind directly to avoid importing the step tactic. -/
import Aeneas.Std.Core.Iter
import Aeneas.Std.Scalar
import Aeneas.Std.SliceIter

namespace Aeneas.Std

open Result core.ops.range WP

/-- Step spec for `IteratorRange.next` on `Range Usize` when `start < end`.
    NOTE: This theorem is more restrictive than necessary — a `_none` variant
    for `start ≥ end` (returning `(none, range)`) should also be provided, and
    both could be unified into a single spec with a conditional postcondition. -/
@[step]
theorem core.iter.range.IteratorRange.next_Usize_spec
    (range : core.ops.range.Range Usize)
    (hlt : range.start.val < range.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range
    ⦃ (opt : Option Usize) (range' : core.ops.range.Range Usize) =>
      opt = some range.start ∧
      range'.start.val = range.start.val + 1 ∧
      range'.end = range.end ⦄ := by
  simp only [core.iter.range.IteratorRange.next,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, core.clone.impls.CloneUsize.clone,
    liftFun1, liftFun2, bind_tc_ok,
    hlt, decide_true, ↓reduceIte]
  have hadd := @UScalar.add_equiv UScalarTy.Usize range.start (1#usize)
  split at hadd
  · rename_i z heq
    obtain ⟨_, hval, _⟩ := hadd
    have hdite : range.start.val + 1 ≤ UScalar.max .Usize := by scalar_tac
    simp only [hdite, ↓reduceDIte, bind_tc_ok, spec_ok, UScalar.ofNatCore_val_eq]
    exact ⟨rfl, by scalar_tac, rfl⟩
  · exfalso; simp [UScalar.inBounds] at hadd; scalar_tac
  · exact hadd.elim

/-- `skipN` on `Range Usize` advances `start.val` by exactly `n`,
    provided `start + n ≤ end` (no early exhaustion). -/
@[step]
theorem core.iter.adapters.step_by.skipN_Range_Usize_spec
    (range : core.ops.range.Range Usize) (n : Nat)
    (hfit : range.start.val + n ≤ range.end.val)
    (hmax : range.start.val + n ≤ Usize.max) :
    core.iter.adapters.step_by.skipN
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) range n
    ⦃ r => r.start.val = range.start.val + n ∧ r.end = range.end ⦄ := by
  induction n generalizing range with
  | zero =>
    unfold core.iter.adapters.step_by.skipN
    simp [spec_ok]
  | succ n ih =>
    unfold core.iter.adapters.step_by.skipN
    apply spec_bind (core.iter.range.IteratorRange.next_Usize_spec range (by omega))
    intro ⟨opt, range'⟩ ⟨_, hstart', hend'⟩
    simp
    split
    · -- none case: impossible (next succeeded)
      simp_all
    · -- some case: apply IH
      apply spec_mono (ih range' (by scalar_tac) (by scalar_tac))
      intro r ⟨h1, h2⟩; exact ⟨by scalar_tac, by rw [h2, hend']⟩

/-- Step spec for `IteratorStepBy.next` on `Range Usize` when `start < end`.
    Requires `start + step_by ≤ end` to ensure the range doesn't exhaust
    during the `skipN` phase. -/
@[step]
theorem core.iter.adapters.step_by.IteratorStepBy.next_range_Usize_step_spec
    (it : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (hstart : it.iter.start.val < it.iter.end.val)
    (hstep : it.step_by.val > 0)
    (hstep_in_range : it.iter.start.val + it.step_by.val ≤ it.iter.end.val) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it
    ⦃ (opt : Option Usize) (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)) =>
      opt = some it.iter.start ∧
      it'.iter.start.val = it.iter.start.val + it.step_by.val ∧
      it'.iter.end = it.iter.end ∧
      it'.step_by = it.step_by ⦄ := by
  unfold core.iter.adapters.step_by.IteratorStepBy.next
  apply spec_bind (core.iter.range.IteratorRange.next_Usize_spec it.iter hstart)
  intro ⟨opt, range'⟩ ⟨hopt, hstart', hend'⟩
  simp only [hopt]
  apply spec_bind
    (skipN_Range_Usize_spec range' (it.step_by.val - 1) (by scalar_tac) (by scalar_tac))
  intro r ⟨h1, h2⟩
  simp only [spec_ok]
  exact ⟨rfl, by scalar_tac, by rw [h2, hend'], rfl⟩

/-- Step spec for `IteratorStepBy.next` on `Range Usize` when `start ≥ end`. -/
@[step]
theorem core.iter.adapters.step_by.IteratorStepBy.next_range_Usize_none_step_spec
    (it : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (hstart : it.iter.start.val ≥ it.iter.end.val) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it
    ⦃ (opt : Option Usize) (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)) =>
      opt = none ∧ it' = it ⦄ := by
  unfold core.iter.adapters.step_by.IteratorStepBy.next
  simp only [core.iter.traits.iterator.IteratorRange,
    core.iter.range.IteratorRange.next,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, core.clone.impls.CloneUsize.clone,
    liftFun1, liftFun2, bind_tc_ok,
    show ¬ (it.iter.start.val < it.iter.end.val) from by omega,
    decide_false, Bool.false_eq_true, ↓reduceIte, spec_ok]
  simp [uncurry'_pair]

/-- General `skipN` on `Range Usize`: start advances by min(n, end - start).
    This covers both the non-exhausting case (start + n ≤ end) and the
    exhausting case (start + n > end, where start saturates at end).
    Requires `start ≤ end` (the range is not already past its end). -/
@[step]
theorem core.iter.adapters.step_by.skipN_Range_Usize_general_spec
    (range : core.ops.range.Range Usize) (n : Nat)
    (hle : range.start.val ≤ range.end.val)
    (hmax : range.end.val ≤ Usize.max) :
    core.iter.adapters.step_by.skipN
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) range n
    ⦃ r => r.start.val = min (range.start.val + n) range.end.val ∧
            r.end = range.end ⦄ := by
  induction n generalizing range with
  | zero =>
    unfold core.iter.adapters.step_by.skipN
    simp only [spec_ok, Nat.add_zero, Nat.min_def]
    simp_all
  | succ n ih =>
    unfold core.iter.adapters.step_by.skipN
    by_cases hlt : range.start.val < range.end.val
    · -- next succeeds
      apply spec_bind (core.iter.range.IteratorRange.next_Usize_spec range hlt)
      intro ⟨opt, range'⟩ ⟨_, hstart', hend'⟩
      simp
      split
      · simp_all
      · apply spec_mono (ih range' (by scalar_tac) (by scalar_tac))
        intro r ⟨h1, h2⟩
        refine ⟨?_, by rw [h2, hend']⟩
        rw [h1, hstart']
        simp only [Nat.min_def]
        split_ifs with h <;> scalar_tac
    · -- range exhausted: start = end, skipN returns identity
      have hse : range.start.val = range.end.val := by scalar_tac
      simp only [core.iter.traits.iterator.IteratorRange,
        core.iter.range.IteratorRange.next,
        core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
        core.cmp.impls.PartialOrdUsize.lt, core.clone.impls.CloneUsize.clone,
        liftFun1, liftFun2, bind_tc_ok,
        show ¬ (range.start.val < range.end.val) from hlt,
        decide_false, Bool.false_eq_true, ↓reduceIte, spec_ok, Nat.min_def]
      simp_all [Nat.min_def]

/-- Step spec for `IteratorStepBy.next` on `Range Usize` (some case, general).
    Only requires `start + step_by ≤ Usize.max` (not `≤ end`).
    After the call, the new start is `min(start + step_by, end)`. -/
@[step]
theorem core.iter.adapters.step_by.IteratorStepBy.next_range_Usize_general_step_spec
    (it : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (hstart : it.iter.start.val < it.iter.end.val)
    (hstep : it.step_by.val > 0) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it
    ⦃ (opt : Option Usize) (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)) =>
      opt = some it.iter.start ∧
      it'.iter.start.val = min (it.iter.start.val + it.step_by.val) it.iter.end.val ∧
      it'.iter.end = it.iter.end ∧
      it'.step_by = it.step_by ⦄ := by
  unfold core.iter.adapters.step_by.IteratorStepBy.next
  apply spec_bind (core.iter.range.IteratorRange.next_Usize_spec it.iter hstart)
  intro ⟨opt, range'⟩ ⟨hopt, hstart', hend'⟩
  simp only [hopt]
  apply spec_bind
    (skipN_Range_Usize_general_spec range' (it.step_by.val - 1) (by scalar_tac) (by scalar_tac))
  intro r ⟨h1, h2⟩
  simp only [spec_ok]
  refine ⟨rfl, ?_, by rw [h2, hend'], rfl⟩
  rw [h1, hstart']
  simp [Nat.min_def]; split_ifs <;> agrind

-- ============================================================================
-- Range<U8> iterator specs
-- ============================================================================

/-- Step spec for `IteratorRange.next` on `Range U8` when `start < end`. -/
@[step]
theorem core.iter.range.IteratorRange.next_U8_spec
    (range : core.ops.range.Range U8)
    (hlt : range.start.val < range.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepU8 range
    ⦃ (opt : Option U8) (range' : core.ops.range.Range U8) =>
      opt = some range.start ∧
      range'.start.val = range.start.val + 1 ∧
      range'.end = range.end ⦄ := by
  simp only [core.iter.range.IteratorRange.next,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdU8.lt, core.clone.impls.CloneU8.clone,
    liftFun1, liftFun2, bind_tc_ok]
  have hfwd : range.start.val + (1#usize).val ≤ UScalar.max .U8 := by scalar_tac
  simp only [hlt, decide_true, ↓reduceIte, hfwd, ↓reduceDIte, bind_tc_ok, spec_ok]
  simp [UScalar.ofNatCore_val_eq]

/-- Step spec for `IteratorRange.next` on `Range U8` when `start ≥ end`. -/
@[step]
theorem core.iter.range.IteratorRange.next_U8_spec_none
    (range : core.ops.range.Range U8)
    (hge : range.start.val ≥ range.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepU8 range
    ⦃ (opt : Option U8) (range' : core.ops.range.Range U8) =>
      opt = none ∧ range' = range ⦄ := by
  simp only [core.iter.range.IteratorRange.next,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdU8.lt, liftFun2,
    show ¬ (range.start.val < range.end.val) from by omega]
  simp [spec_ok]

-- ============================================================================
-- Enumerate iterator specs (generic)
-- ============================================================================

/-- Step spec for `Enumerate.next` — some case.
    When the inner iterator yields `some a`, enumerate returns `(count, a)`
    and increments count. -/
@[step]
theorem core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
    {I : Type} {Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I)
    (a : Item) (iter' : I)
    (h_inner : IteratorInst.next self.iter ⦃ p =>
      p.1 = some a ∧ p.2 = iter' ⦄)
    (h_count : self.count.val + 1 ≤ Usize.max) :
    core.iter.adapters.enumerate.IteratorEnumerate.next IteratorInst self
    ⦃ (opt : Option (Usize × Item)) (self' : core.iter.adapters.enumerate.Enumerate I) =>
      opt = some (self.count, a) ∧
      self'.iter = iter' ∧
      self'.count.val = self.count.val + 1 ⦄ := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  apply spec_bind h_inner
  intro ⟨opt, it⟩ ⟨hopt, hit⟩
  subst hopt; subst hit
  have hadd := @UScalar.add_equiv UScalarTy.Usize self.count (1#usize)
  split at hadd
  · rename_i z heq
    obtain ⟨_, hval, _⟩ := hadd
    simp [heq, bind_tc_ok, spec_ok, uncurry', hval]
  · exfalso; simp [UScalar.inBounds] at hadd; scalar_tac
  · exact hadd.elim

/-- Step spec for `Enumerate.next` — none case.
    When the inner iterator yields `none`, enumerate propagates none. -/
@[step]
theorem core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
    {I : Type} {Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I)
    (iter' : I)
    (h_inner : IteratorInst.next self.iter ⦃ p =>
      p.1 = none ∧ p.2 = iter' ⦄) :
    core.iter.adapters.enumerate.IteratorEnumerate.next IteratorInst self
    ⦃ (opt : Option (Usize × Item)) (self' : core.iter.adapters.enumerate.Enumerate I) =>
      opt = none ∧
      self'.iter = iter' ∧
      self'.count = self.count ⦄ := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  apply spec_bind h_inner
  intro ⟨opt, it⟩ ⟨hopt, hit⟩
  subst hopt; subst hit
  simp [spec_ok, uncurry']

-- ============================================================================
-- Take(ChunksExact) iterator spec
-- ============================================================================

/-- Step spec for `Take::next` applied to `ChunksExact<T>`.
    When `n = 0`, returns `none` unchanged.
    When `n > 0`, delegates to `ChunksExact::next` and decrements `n`. -/
@[step]
theorem core.iter.adapters.take.IteratorTake.next_ChunksExact_spec {T : Type}
    (iter : core.iter.adapters.take.Take (core.slice.iter.ChunksExact T)) :
    core.iter.adapters.take.IteratorTake.next
      (core.iter.traits.iterator.IteratorChunksExact T) iter
    ⦃ (result : Option (Slice T))
      (iter' : core.iter.adapters.take.Take (core.slice.iter.ChunksExact T)) =>
      if iter.n.val = 0 then
        result = none ∧ iter' = iter
      else
        match iter.iter.chunks with
        | [] => result = none ∧ iter'.iter.chunks = [] ∧ iter'.n.val = iter.n.val - 1
        | chunk :: rest =>
          result = some chunk ∧ iter'.iter.chunks = rest ∧ iter'.n.val = iter.n.val - 1 ⦄ := by
  simp only [core.iter.adapters.take.IteratorTake.next]
  split
  · simp [spec_ok]
  · rename_i hne
    simp only [core.slice.iter.IteratorChunksExact.next]
    have hsub : ∃ z, iter.n - 1#usize = ok z ∧ z.val = iter.n.val - 1 := by
      have h := @UScalar.sub_equiv .Usize iter.n (1#usize)
      split at h
      next z heq =>
        obtain ⟨_, hval, _⟩ := h
        exact ⟨z, heq, by scalar_tac⟩
      next heq =>
        exfalso; scalar_tac
      next => exact h.elim
    obtain ⟨z, hsub_eq, hzval⟩ := hsub
    simp only [hsub_eq, bind_tc_ok]
    split <;> simp_all

end Aeneas.Std
