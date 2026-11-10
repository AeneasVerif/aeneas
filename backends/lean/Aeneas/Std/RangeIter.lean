/- Step specs for Range/StepBy iterators on Usize.
   These use WP.spec_bind directly to avoid importing the step tactic. -/
module
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.Scalar
public import Aeneas.Std.SliceIter
public import Aeneas.Std.RangeContains
public section

namespace Aeneas.Std

open Result core.ops.range WP ScalarElab

-- ============================================================================
-- Generic UScalar Range/StepBy iterator specs
-- ============================================================================

/-- Generic `IteratorRange.next` on `Range (UScalar ty)`, some case
    (`start < end`): yields `some start` and advances by one. -/
theorem core.iter.range.IteratorRange.next_UScalar_some_spec {ty : UScalarTy}
    {cloneInst : core.clone.Clone (UScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)}
    (h_clone : ∀ x : UScalar ty, cloneInst.clone (SharedBorrow.mk x) = ok x)
    (h_lt : ∀ a b : UScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (range : MutBorrow (core.ops.range.Range (UScalar ty)))
    (hlt : range.val.start.val < range.val.end.val) :
    core.iter.range.IteratorRange.next
        (core.iter.range.UScalarStep ty cloneInst partialOrdInst) range
    ⦃ (opt : Option (UScalar ty)) (range' : core.ops.range.Range (UScalar ty)) =>
      opt = some range.val.start ∧
      range'.start.val = range.val.start.val + 1 ∧
      range'.end = range.val.end ⦄ := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked, bind_ok,
    h_lt, h_clone, hlt, decide_true, ↓reduceIte]
  have hfwd : range.val.start.val + (1#usize).val ≤ UScalar.max ty := by scalar_tac
  simp only [hfwd, ↓reduceDIte, bind_ok, spec_ok]
  simp [UScalar.ofNatCore_val_eq]

/-- Generic `IteratorRange.next` on `Range (UScalar ty)`, none case
    (`start ≥ end`): yields `none`, leaves the range unchanged. -/
theorem core.iter.range.IteratorRange.next_UScalar_none_spec {ty : UScalarTy}
    {cloneInst : core.clone.Clone (UScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)}
    (h_lt : ∀ a b : UScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (range : MutBorrow (core.ops.range.Range (UScalar ty)))
    (hge : range.val.start.val ≥ range.val.end.val) :
    core.iter.range.IteratorRange.next
        (core.iter.range.UScalarStep ty cloneInst partialOrdInst) range
    ⦃ (opt : Option (UScalar ty)) (range' : core.ops.range.Range (UScalar ty)) =>
      opt = none ∧ range' = range.val ⦄ := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked, bind_ok, h_lt,
    show ¬ (range.val.start.val < range.val.end.val) from by omega,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  simp [spec_ok]

/-- Generic merged `IteratorRange.next` on `Range (UScalar ty)`: conditional
    postcondition combining the some and none cases. -/
theorem core.iter.range.IteratorRange.next_UScalar_spec {ty : UScalarTy}
    {cloneInst : core.clone.Clone (UScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)}
    (h_clone : ∀ x : UScalar ty, cloneInst.clone (SharedBorrow.mk x) = ok x)
    (h_lt : ∀ a b : UScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (range : MutBorrow (core.ops.range.Range (UScalar ty))) :
    core.iter.range.IteratorRange.next
        (core.iter.range.UScalarStep ty cloneInst partialOrdInst) range
    ⦃ (opt : Option (UScalar ty)) (range' : core.ops.range.Range (UScalar ty)) =>
      (if range.val.start.val < range.val.end.val then
         opt = some range.val.start ∧ range'.start.val = range.val.start.val + 1
       else
         opt = none ∧ range'.start = range.val.start) ∧
      range'.end = range.val.end ⦄ := by
  by_cases h : range.val.start.val < range.val.end.val
  · simp only [h, ↓reduceIte]
    apply spec_mono
      (core.iter.range.IteratorRange.next_UScalar_some_spec h_clone h_lt range h)
    rintro ⟨opt, range'⟩ ⟨h1, h2, h3⟩
    simp only [uncurry'_pair]
    exact ⟨⟨h1, h2⟩, h3⟩
  · simp only [h, ↓reduceIte]
    apply spec_mono
      (core.iter.range.IteratorRange.next_UScalar_none_spec h_lt range (by omega))
    rintro ⟨opt, range'⟩ ⟨rfl, rfl⟩
    simp [uncurry'_pair]

-- Generic `IteratorRange.next` on the signed ranges

/-- Generic `IteratorRange.next` on `Range (IScalar ty)`, some case (`start < end`): yields
`some start` and advances by one. -/
theorem core.iter.range.IteratorRange.next_IScalar_some_spec {ty : IScalarTy}
    {cloneInst : core.clone.Clone (IScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (IScalar ty) (IScalar ty)}
    (h_clone : ∀ x : IScalar ty, cloneInst.clone (SharedBorrow.mk x) = ok x)
    (h_lt : ∀ a b : IScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (range : MutBorrow (core.ops.range.Range (IScalar ty)))
    (hlt : range.val.start.val < range.val.end.val) :
    core.iter.range.IteratorRange.next
        (core.iter.range.IScalarStep ty cloneInst partialOrdInst) range
    ⦃ (opt : Option (IScalar ty)) (range' : core.ops.range.Range (IScalar ty)) =>
      opt = some range.val.start ∧
      range'.start.val = range.val.start.val + 1 ∧
      range'.end = range.val.end ⦄ := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.IScalarStep,
    core.iter.range.IScalarStep.forward_checked, bind_ok,
    h_lt, h_clone, hlt, decide_true, ↓reduceIte]
  have hfwd : range.val.start.val + (1#usize).val ≤ IScalar.max ty := by
    have := range.val.end.hmax; scalar_tac
  simp only [hfwd, ↓reduceDIte, bind_ok, spec_ok]
  refine ⟨rfl, ?_, rfl⟩
  rw [IScalar.ofInt_val_eq]
  simp

/-- Generic `IteratorRange.next` on `Range (IScalar ty)`, none case (`start ≥ end`). -/
theorem core.iter.range.IteratorRange.next_IScalar_none_spec {ty : IScalarTy}
    {cloneInst : core.clone.Clone (IScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (IScalar ty) (IScalar ty)}
    (h_lt : ∀ a b : IScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (range : MutBorrow (core.ops.range.Range (IScalar ty)))
    (hge : range.val.start.val ≥ range.val.end.val) :
    core.iter.range.IteratorRange.next
        (core.iter.range.IScalarStep ty cloneInst partialOrdInst) range
    ⦃ (opt : Option (IScalar ty)) (range' : core.ops.range.Range (IScalar ty)) =>
      opt = none ∧ range' = range.val ⦄ := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.IScalarStep,
    core.iter.range.IScalarStep.forward_checked, bind_ok, h_lt,
    show ¬ (range.val.start.val < range.val.end.val) from by omega,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  simp [spec_ok]

/-- Generic merged `IteratorRange.next` on `Range (IScalar ty)`. -/
theorem core.iter.range.IteratorRange.next_IScalar_spec {ty : IScalarTy}
    {cloneInst : core.clone.Clone (IScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (IScalar ty) (IScalar ty)}
    (h_clone : ∀ x : IScalar ty, cloneInst.clone (SharedBorrow.mk x) = ok x)
    (h_lt : ∀ a b : IScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (range : MutBorrow (core.ops.range.Range (IScalar ty))) :
    core.iter.range.IteratorRange.next
        (core.iter.range.IScalarStep ty cloneInst partialOrdInst) range
    ⦃ (opt : Option (IScalar ty)) (range' : core.ops.range.Range (IScalar ty)) =>
      (if range.val.start.val < range.val.end.val then
         opt = some range.val.start ∧ range'.start.val = range.val.start.val + 1
       else
         opt = none ∧ range'.start = range.val.start) ∧
      range'.end = range.val.end ⦄ := by
  by_cases h : range.val.start.val < range.val.end.val
  · simp only [h, ↓reduceIte]
    apply spec_mono
      (core.iter.range.IteratorRange.next_IScalar_some_spec h_clone h_lt range h)
    rintro ⟨opt, range'⟩ ⟨h1, h2, h3⟩
    simp only [uncurry'_pair]
    exact ⟨⟨h1, h2⟩, h3⟩
  · simp only [h, ↓reduceIte]
    apply spec_mono
      (core.iter.range.IteratorRange.next_IScalar_none_spec h_lt range (by omega))
    rintro ⟨opt, range'⟩ ⟨rfl, rfl⟩
    simp [uncurry'_pair]

/-- Generic `skipN` on `Range (UScalar ty)`, saturating version: start advances
    by `min(n, end - start)`. Requires `start ≤ end`. -/
theorem core.iter.adapters.step_by.skipN_Range_UScalar_spec {ty : UScalarTy}
    {cloneInst : core.clone.Clone (UScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)}
    (h_clone : ∀ x : UScalar ty, cloneInst.clone (SharedBorrow.mk x) = ok x)
    (h_lt : ∀ a b : UScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (range : core.ops.range.Range (UScalar ty)) (n : Nat)
    (hle : range.start.val ≤ range.end.val)
    (hmax : range.end.val ≤ UScalar.max ty) :
    core.iter.adapters.step_by.skipN
      (core.iter.traits.iterator.IteratorRange
        (core.iter.range.UScalarStep ty cloneInst partialOrdInst)) range n
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
    · apply spec_bind
        (core.iter.range.IteratorRange.next_UScalar_some_spec h_clone h_lt (MutBorrow.mk range) hlt)
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
    · have hse : range.start.val = range.end.val := by scalar_tac
      simp only [core.iter.traits.iterator.IteratorRange,
        core.iter.range.IteratorRange.next,
        core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
        h_lt, bind_ok,
        show ¬ (range.start.val < range.end.val) from hlt,
        decide_false, Bool.false_eq_true, ↓reduceIte, Nat.min_def]
      simp_all [Nat.min_def]

/-- Generic `IteratorStepBy.next` on `Range (UScalar ty)`, non-saturating some
    case (`start < end` and `start + step_by ≤ end`). -/
theorem core.iter.adapters.step_by.IteratorStepBy.next_Range_UScalar_some_spec
    {ty : UScalarTy}
    {cloneInst : core.clone.Clone (UScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)}
    (h_clone : ∀ x : UScalar ty, cloneInst.clone (SharedBorrow.mk x) = ok x)
    (h_lt : ∀ a b : UScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (it : MutBorrow (core.iter.adapters.step_by.StepBy (core.ops.range.Range (UScalar ty))))
    (hstart : it.val.iter.start.val < it.val.iter.end.val)
    (hstep : it.val.step_by.val > 0)
    (hstep_in_range : it.val.iter.start.val + it.val.step_by.val ≤ it.val.iter.end.val) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange
        (core.iter.range.UScalarStep ty cloneInst partialOrdInst)) it
    ⦃ (opt : Option (UScalar ty))
      (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range (UScalar ty))) =>
      opt = some it.val.iter.start ∧
      it'.iter.start.val = it.val.iter.start.val + it.val.step_by.val ∧
      it'.iter.end = it.val.iter.end ∧
      it'.step_by = it.val.step_by ⦄ := by
  unfold core.iter.adapters.step_by.IteratorStepBy.next
  apply spec_bind
    (core.iter.range.IteratorRange.next_UScalar_some_spec h_clone h_lt (MutBorrow.mk it.val.iter) hstart)
  intro ⟨opt, range'⟩ ⟨hopt, hstart', hend'⟩
  simp only [hopt]
  apply spec_bind
    (core.iter.adapters.step_by.skipN_Range_UScalar_spec h_clone h_lt range'
      (it.val.step_by.val - 1) (by scalar_tac) (by scalar_tac))
  intro r ⟨h1, h2⟩
  simp only [spec_ok]
  refine ⟨rfl, ?_, by rw [h2, hend'], rfl⟩
  rw [h1, hstart', show range'.end = it.val.iter.end from hend']
  simp only [Nat.min_def]; split_ifs <;> scalar_tac

/-- Generic `IteratorStepBy.next` on `Range (UScalar ty)`, none case
    (`start ≥ end`): yields `none`, leaves the iterator unchanged. -/
theorem core.iter.adapters.step_by.IteratorStepBy.next_Range_UScalar_none_spec
    {ty : UScalarTy}
    {cloneInst : core.clone.Clone (UScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)}
    (h_lt : ∀ a b : UScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (it : MutBorrow (core.iter.adapters.step_by.StepBy (core.ops.range.Range (UScalar ty))))
    (hstart : it.val.iter.start.val ≥ it.val.iter.end.val) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange
        (core.iter.range.UScalarStep ty cloneInst partialOrdInst)) it
    ⦃ (opt : Option (UScalar ty))
      (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range (UScalar ty))) =>
      opt = none ∧ it' = it.val ⦄ := by
  unfold core.iter.adapters.step_by.IteratorStepBy.next
  simp only [core.iter.traits.iterator.IteratorRange,
    core.iter.range.IteratorRange.next,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    h_lt, bind_ok,
    show ¬ (it.val.iter.start.val < it.val.iter.end.val) from by omega,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  simp [uncurry'_pair]

/-- Generic merged `IteratorStepBy.next` on `Range (UScalar ty)` (saturating,
    conditional postcondition combining the some and none cases). -/
theorem core.iter.adapters.step_by.IteratorStepBy.next_Range_UScalar_spec
    {ty : UScalarTy}
    {cloneInst : core.clone.Clone (UScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)}
    (h_clone : ∀ x : UScalar ty, cloneInst.clone (SharedBorrow.mk x) = ok x)
    (h_lt : ∀ a b : UScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (it : MutBorrow (core.iter.adapters.step_by.StepBy (core.ops.range.Range (UScalar ty))))
    (hstep : it.val.step_by.val > 0) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange
        (core.iter.range.UScalarStep ty cloneInst partialOrdInst)) it
    ⦃ (opt : Option (UScalar ty))
      (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range (UScalar ty))) =>
      (if it.val.iter.start.val < it.val.iter.end.val then
         opt = some it.val.iter.start ∧
         it'.iter.start.val = min (it.val.iter.start.val + it.val.step_by.val) it.val.iter.end.val
       else
         opt = none ∧ it'.iter.start = it.val.iter.start) ∧
      it'.iter.end = it.val.iter.end ∧
      it'.step_by = it.val.step_by ⦄ := by
  by_cases h : it.val.iter.start.val < it.val.iter.end.val
  · simp only [h, ↓reduceIte]
    unfold core.iter.adapters.step_by.IteratorStepBy.next
    apply spec_bind
      (core.iter.range.IteratorRange.next_UScalar_some_spec h_clone h_lt (MutBorrow.mk it.val.iter) h)
    intro ⟨opt, range'⟩ ⟨hopt, hstart', hend'⟩
    simp only [hopt]
    apply spec_bind
      (core.iter.adapters.step_by.skipN_Range_UScalar_spec h_clone h_lt range'
        (it.val.step_by.val - 1) (by scalar_tac) (by scalar_tac))
    intro r ⟨h1, h2⟩
    simp only [spec_ok]
    refine ⟨⟨rfl, ?_⟩, by rw [h2, hend'], rfl⟩
    rw [h1, hstart']
    simp [Nat.min_def]; split_ifs <;> agrind
  · simp only [h, ↓reduceIte]
    apply spec_mono
      (core.iter.adapters.step_by.IteratorStepBy.next_Range_UScalar_none_spec h_lt it
        (by omega))
    rintro ⟨opt, it'⟩ ⟨rfl, rfl⟩
    simp [uncurry'_pair]

-- ============================================================================
-- Per-type specializations
-- ============================================================================

-- `IteratorRange.next`, some case (`start < end`): yields `some start`, advances by one.
uscalar
theorem core.iter.range.IteratorRange.next_'S_some_spec
    (range : MutBorrow (core.ops.range.Range «%S»))
    (hlt : range.val.start.val < range.val.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.Step'S range
    ⦃ (opt : Option «%S») (range' : core.ops.range.Range «%S») =>
      opt = some range.val.start ∧
      range'.start.val = range.val.start.val + 1 ∧
      range'.end = range.val.end ⦄ :=
  core.iter.range.IteratorRange.next_UScalar_some_spec
    (by simp) (by intros; rfl) range hlt

-- `IteratorRange.next`, none case (`start ≥ end`): yields `none`, range unchanged.
uscalar
theorem core.iter.range.IteratorRange.next_'S_none_spec
    (range : MutBorrow (core.ops.range.Range «%S»))
    (hge : range.val.start.val ≥ range.val.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.Step'S range
    ⦃ (opt : Option «%S») (range' : core.ops.range.Range «%S») =>
      opt = none ∧ range' = range.val ⦄ :=
  core.iter.range.IteratorRange.next_UScalar_none_spec
    (by intros; rfl) range hge

-- Merged `@[step]` spec for `IteratorRange.next` (conditional postcondition).
uscalar
@[step]
theorem core.iter.range.IteratorRange.next_'S_spec
    (range : MutBorrow (core.ops.range.Range «%S»)) :
    core.iter.range.IteratorRange.next core.iter.range.Step'S range
    ⦃ (opt : Option «%S») (range' : core.ops.range.Range «%S») =>
      (if range.val.start.val < range.val.end.val then
         opt = some range.val.start ∧ range'.start.val = range.val.start.val + 1
       else
         opt = none ∧ range'.start = range.val.start) ∧
      range'.end = range.val.end ⦄ :=
  core.iter.range.IteratorRange.next_UScalar_spec
    (by simp) (by intros; rfl) range

-- `IteratorRange.next` on the signed ranges (`for i in a..b` with `a b : isize`, ...), some case.
iscalar
theorem core.iter.range.IteratorRange.next_'S_some_spec
    (range : MutBorrow (core.ops.range.Range «%S»))
    (hlt : range.val.start.val < range.val.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.Step'S range
    ⦃ (opt : Option «%S») (range' : core.ops.range.Range «%S») =>
      opt = some range.val.start ∧
      range'.start.val = range.val.start.val + 1 ∧
      range'.end = range.val.end ⦄ :=
  core.iter.range.IteratorRange.next_IScalar_some_spec (by simp) (by intros; rfl) range hlt

-- `IteratorRange.next` on the signed ranges, none case.
iscalar
theorem core.iter.range.IteratorRange.next_'S_none_spec
    (range : MutBorrow (core.ops.range.Range «%S»))
    (hge : range.val.start.val ≥ range.val.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.Step'S range
    ⦃ (opt : Option «%S») (range' : core.ops.range.Range «%S») =>
      opt = none ∧ range' = range.val ⦄ :=
  core.iter.range.IteratorRange.next_IScalar_none_spec (by intros; rfl) range hge

-- Merged `@[step]` spec for `IteratorRange.next` on the signed ranges.
iscalar
@[step]
theorem core.iter.range.IteratorRange.next_'S_spec
    (range : MutBorrow (core.ops.range.Range «%S»)) :
    core.iter.range.IteratorRange.next core.iter.range.Step'S range
    ⦃ (opt : Option «%S») (range' : core.ops.range.Range «%S») =>
      (if range.val.start.val < range.val.end.val then
         opt = some range.val.start ∧ range'.start.val = range.val.start.val + 1
       else
         opt = none ∧ range'.start = range.val.start) ∧
      range'.end = range.val.end ⦄ :=
  core.iter.range.IteratorRange.next_IScalar_spec (by simp) (by intros; rfl) range

-- Saturating `skipN`: start advances by `min(n, end - start)`.
uscalar
@[step]
theorem core.iter.adapters.step_by.skipN_Range_'S_spec
    (range : core.ops.range.Range «%S») (n : Nat)
    (hle : range.start.val ≤ range.end.val)
    (hmax : range.end.val ≤ «%S».max) :
    core.iter.adapters.step_by.skipN
      (core.iter.traits.iterator.IteratorRange core.iter.range.Step'S) range n
    ⦃ r => r.start.val = min (range.start.val + n) range.end.val ∧
            r.end = range.end ⦄ :=
  core.iter.adapters.step_by.skipN_Range_UScalar_spec
    (by simp) (by intros; rfl) range n hle (by scalar_tac)

-- `IteratorStepBy.next`, non-saturating some case (`start + step_by ≤ end`).
uscalar
theorem core.iter.adapters.step_by.IteratorStepBy.next_Range_'S_some_spec
    (it : MutBorrow (core.iter.adapters.step_by.StepBy (core.ops.range.Range «%S»)))
    (hstart : it.val.iter.start.val < it.val.iter.end.val)
    (hstep : it.val.step_by.val > 0)
    (hstep_in_range : it.val.iter.start.val + it.val.step_by.val ≤ it.val.iter.end.val) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.Step'S) it
    ⦃ (opt : Option «%S») (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range «%S»)) =>
      opt = some it.val.iter.start ∧
      it'.iter.start.val = it.val.iter.start.val + it.val.step_by.val ∧
      it'.iter.end = it.val.iter.end ∧
      it'.step_by = it.val.step_by ⦄ :=
  core.iter.adapters.step_by.IteratorStepBy.next_Range_UScalar_some_spec
    (by simp) (by intros; rfl) it hstart hstep hstep_in_range

-- `IteratorStepBy.next`, none case (`start ≥ end`): yields `none`, iterator unchanged.
uscalar
theorem core.iter.adapters.step_by.IteratorStepBy.next_Range_'S_none_spec
    (it : MutBorrow (core.iter.adapters.step_by.StepBy (core.ops.range.Range «%S»)))
    (hstart : it.val.iter.start.val ≥ it.val.iter.end.val) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.Step'S) it
    ⦃ (opt : Option «%S») (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range «%S»)) =>
      opt = none ∧ it' = it.val ⦄ :=
  core.iter.adapters.step_by.IteratorStepBy.next_Range_UScalar_none_spec
    (by intros; rfl) it hstart

-- Merged `@[step]` spec for `IteratorStepBy.next` (saturating, conditional).
uscalar
@[step]
theorem core.iter.adapters.step_by.IteratorStepBy.next_Range_'S_spec
    (it : MutBorrow (core.iter.adapters.step_by.StepBy (core.ops.range.Range «%S»)))
    (hstep : it.val.step_by.val > 0) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.Step'S) it
    ⦃ (opt : Option «%S») (it' : core.iter.adapters.step_by.StepBy (core.ops.range.Range «%S»)) =>
      (if it.val.iter.start.val < it.val.iter.end.val then
         opt = some it.val.iter.start ∧
         it'.iter.start.val = min (it.val.iter.start.val + it.val.step_by.val) it.val.iter.end.val
       else
         opt = none ∧ it'.iter.start = it.val.iter.start) ∧
      it'.iter.end = it.val.iter.end ∧
      it'.step_by = it.val.step_by ⦄ :=
  core.iter.adapters.step_by.IteratorStepBy.next_Range_UScalar_spec
    (by simp) (by intros; rfl) it hstep

-- ============================================================================
-- Enumerate iterator specs (generic)
-- ============================================================================

/-- `Enumerate.next` — some case.  No `@[step]` — see the merged `next_spec`.
    When the inner iterator yields `some a`, enumerate returns `(count, a)`
    and increments count. -/
theorem core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
    {I : Type _} {Item : Type _}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : MutBorrow (core.iter.adapters.enumerate.Enumerate I))
    (a : Item) (iter' : I)
    (h_inner : IteratorInst.next (MutBorrow.mk self.val.iter) ⦃ p =>
      p.1 = some a ∧ p.2 = iter' ⦄)
    (h_count : self.val.count.val + 1 ≤ Usize.max) :
    core.iter.adapters.enumerate.IteratorEnumerate.next IteratorInst self
    ⦃ (opt : Option (Usize × Item)) (self' : core.iter.adapters.enumerate.Enumerate I) =>
      opt = some (self.val.count, a) ∧
      self'.iter = iter' ∧
      self'.count.val = self.val.count.val + 1 ⦄ := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  apply spec_bind h_inner
  intro ⟨opt, it⟩ ⟨hopt, hit⟩
  subst hopt; subst hit
  have hadd := @UScalar.add_equiv UScalarTy.Usize self.val.count (1#usize)
  split at hadd
  · rename_i z heq
    simp at heq
    obtain ⟨_, hval, _⟩ := hadd
    simp [heq, bind_ok, spec_ok, uncurry', hval]
  · exfalso; simp [UScalar.inBounds] at hadd; scalar_tac
  · exact hadd.elim

/-- `Enumerate.next` — none case.  No `@[step]` — see the merged `next_spec`.
    When the inner iterator yields `none`, enumerate propagates none. -/
theorem core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
    {I : Type _} {Item : Type _}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : MutBorrow (core.iter.adapters.enumerate.Enumerate I))
    (iter' : I)
    (h_inner : IteratorInst.next (MutBorrow.mk self.val.iter) ⦃ p =>
      p.1 = none ∧ p.2 = iter' ⦄) :
    core.iter.adapters.enumerate.IteratorEnumerate.next IteratorInst self
    ⦃ (opt : Option (Usize × Item)) (self' : core.iter.adapters.enumerate.Enumerate I) =>
      opt = none ∧
      self'.iter = iter' ∧
      self'.count = self.val.count ⦄ := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  apply spec_bind h_inner
  intro ⟨opt, it⟩ ⟨hopt, hit⟩
  subst hopt; subst hit
  simp [spec_ok, uncurry']

/-- Merged `@[step]` spec for `Enumerate.next` (both cases combined, branching
    on the inner iterator's yielded option `o`).  Single `@[step]` entry point;
    the `next_some_spec` / `next_none_spec` variants remain available for
    explicit use. -/
@[step]
theorem core.iter.adapters.enumerate.IteratorEnumerate.next_spec
    {I : Type _} {Item : Type _}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : MutBorrow (core.iter.adapters.enumerate.Enumerate I))
    (o : Option Item) (iter' : I)
    (h_inner : IteratorInst.next (MutBorrow.mk self.val.iter) ⦃ p =>
      p.1 = o ∧ p.2 = iter' ⦄)
    (h_count : self.val.count.val + 1 ≤ Usize.max) :
    core.iter.adapters.enumerate.IteratorEnumerate.next IteratorInst self
    ⦃ (opt : Option (Usize × Item)) (self' : core.iter.adapters.enumerate.Enumerate I) =>
      (match o with
       | some a => opt = some (self.val.count, a) ∧ self'.count.val = self.val.count.val + 1
       | none => opt = none ∧ self'.count = self.val.count) ∧
      self'.iter = iter' ⦄ := by
  cases o with
  | some a =>
    apply spec_mono
      (core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
        IteratorInst self a iter' h_inner h_count)
    rintro ⟨opt, self'⟩ ⟨h1, h2, h3⟩
    simp only [uncurry'_pair]
    exact ⟨⟨h1, h3⟩, h2⟩
  | none =>
    apply spec_mono
      (core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
        IteratorInst self iter' h_inner)
    rintro ⟨opt, self'⟩ ⟨h1, h2, h3⟩
    simp only [uncurry'_pair]
    exact ⟨⟨h1, h3⟩, h2⟩

-- ============================================================================
-- Take(ChunksExact) iterator spec
-- ============================================================================

/-- Step spec for `Take::next` applied to `ChunksExact<T>`.
    When `n = 0`, returns `none` unchanged.
    When `n > 0`, delegates to `ChunksExact::next` and decrements `n`. -/
@[step]
theorem core.iter.adapters.take.IteratorTake.next_ChunksExact_spec {T : Type _}
    (iter : MutBorrow (core.iter.adapters.take.Take (core.slice.iter.ChunksExact T))) :
    core.iter.adapters.take.IteratorTake.next
      (core.iter.traits.iterator.IteratorChunksExact T) iter
    ⦃ (result : Option (SharedBorrow (Slice T)))
      (iter' : core.iter.adapters.take.Take (core.slice.iter.ChunksExact T)) =>
      if iter.val.n.val = 0 then
        result = none ∧ iter' = iter.val
      else
        match iter.val.iter.chunks with
        | [] => result = none ∧ iter'.iter.chunks = [] ∧ iter'.n.val = iter.val.n.val - 1
        | chunk :: rest =>
          result = some ⟨chunk⟩ ∧ iter'.iter.chunks = rest ∧ iter'.n.val = iter.val.n.val - 1 ⦄ := by
  simp only [core.iter.adapters.take.IteratorTake.next]
  split
  · simp [spec_ok]
  · rename_i hne
    simp only [core.slice.iter.IteratorChunksExact.next]
    have hsub : ∃ z, iter.val.n - 1#usize = ok z ∧ z.val = iter.val.n.val - 1 := by
      have h := @UScalar.sub_equiv .Usize iter.val.n (1#usize)
      split at h
      next z heq =>
        obtain ⟨_, hval, _⟩ := h
        simp at heq
        exact ⟨z, heq, by scalar_tac⟩
      next heq =>
        exfalso; scalar_tac
      next => exact h.elim
    obtain ⟨z, hsub_eq, hzval⟩ := hsub
    simp only [hsub_eq, bind_ok]
    split <;> simp_all

-- ============================================================================
-- Zip<A, B> and RangeInclusive<A> iterator specs
-- ============================================================================

/-- `RangeInclusive::new a b` yields `⟨a, b, exhausted := false⟩`. -/
@[step]
theorem core.ops.range.RangeInclusive.new_spec {Idx : Type _} (a b : Idx) :
    core.ops.range.RangeInclusive.new a b
    ⦃ (r : core.ops.range.RangeInclusive Idx) =>
      r.start = a ∧ r.«end» = b ∧ r.exhausted = false ⦄ := by
  simp [core.ops.range.RangeInclusive.new, spec_ok]

/-- Generic `RangeInclusive<UScalar ty>::next`: conditional spec for the three
    cases (empty ⇒ `none`; iterating `start < end` ⇒ yield+advance;
    `start == end` ⇒ yield once then mark exhausted).  `h_lt` says the bundled
    `PartialOrd.lt` is `·.val < ·.val` (discharged by `rfl` per concrete type). -/
theorem core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_UScalar_spec
    {ty : UScalarTy}
    {cloneInst : core.clone.Clone (UScalar ty)}
    {partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)}
    (h_clone : ∀ x : UScalar ty, cloneInst.clone (SharedBorrow.mk x) = ok x)
    (h_lt : ∀ a b : UScalar ty,
      partialOrdInst.lt (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val < b.val)))
    (h_le : ∀ a b : UScalar ty,
      partialOrdInst.le (SharedBorrow.mk a) (SharedBorrow.mk b) = ok (decide (a.val ≤ b.val)))
    (r : MutBorrow (core.ops.range.RangeInclusive (UScalar ty))) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      (core.iter.range.UScalarStep ty cloneInst partialOrdInst) r
    ⦃ (o : Option (UScalar ty)) (r' : core.ops.range.RangeInclusive (UScalar ty)) =>
      if r.val.exhausted ∨ r.val.«end».val < r.val.start.val then
        o = none ∧ r' = r.val
      else if r.val.start.val < r.val.«end».val then
        o = some r.val.start ∧ r'.start.val = r.val.start.val + 1 ∧
        r'.«end» = r.val.«end» ∧ r'.exhausted = false
      else
        o = some r.val.start ∧ r'.start = r.val.start ∧
        r'.«end» = r.val.«end» ∧ r'.exhausted = true ⦄ := by
  have h_empty : core.ops.range.RangeInclusive.is_empty partialOrdInst (SharedBorrow.mk r.val)
      = ok (r.val.exhausted || decide (r.val.«end».val < r.val.start.val)) := by
    unfold core.ops.range.RangeInclusive.is_empty
    by_cases he : r.val.exhausted = true
    · simp [he]
    · simp only [Bool.not_eq_true] at he
      simp only [he, Bool.false_or, h_le, bind_ok]
      simp [pure, ← decide_not]
  unfold core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
  simp only [core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked, h_lt, h_clone, bind_ok, h_empty]
  by_cases hexh : r.val.exhausted = true
  · simp only [hexh, Bool.true_or, ↓reduceIte, spec_ok, true_or]
    simp
  · by_cases hgt : r.val.«end».val < r.val.start.val
    · have : (r.val.exhausted || decide (r.val.«end».val < r.val.start.val)) = true := by simp [hgt]
      simp only [this, ↓reduceIte, spec_ok]
      simp [hexh, hgt]
    · have hguard : (r.val.exhausted || decide (r.val.«end».val < r.val.start.val)) = false := by
        simp only [Bool.eq_false_iff, ne_eq, Bool.or_eq_true, decide_eq_true_eq, not_or]
        exact ⟨hexh, hgt⟩
      have hnotempty : ¬ (r.val.exhausted = true ∨ r.val.«end».val < r.val.start.val) := by
        push Not; exact ⟨hexh, Nat.le_of_not_lt hgt⟩
      simp only [hguard, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt : r.val.start.val < r.val.«end».val
      · simp only [hlt, decide_true, ↓reduceIte]
        have hfwd : r.val.start.val + (1#usize).val ≤ UScalar.max ty := by scalar_tac
        simp only [hfwd, ↓reduceDIte, bind_ok]
        simp only [spec_ok, hnotempty, ↓reduceIte, UScalar.ofNatCore_val_eq]
        exact ⟨rfl, by scalar_tac, rfl, by simpa using hexh⟩
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
        simp only [spec_ok, hnotempty, ↓reduceIte]
        exact ⟨rfl, rfl, rfl, rfl⟩

-- Per-type specializations of `next` for every unsigned scalar.
uscalar
@[step]
theorem core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_'S_spec
    (r : MutBorrow (core.ops.range.RangeInclusive «%S»)) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.Step'S r
    ⦃ (o : Option «%S») (r' : core.ops.range.RangeInclusive «%S») =>
      if r.val.exhausted ∨ r.val.«end».val < r.val.start.val then
        o = none ∧ r' = r.val
      else if r.val.start.val < r.val.«end».val then
        o = some r.val.start ∧ r'.start.val = r.val.start.val + 1 ∧
        r'.«end» = r.val.«end» ∧ r'.exhausted = false
      else
        o = some r.val.start ∧ r'.start = r.val.start ∧
        r'.«end» = r.val.«end» ∧ r'.exhausted = true ⦄ :=
  core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_UScalar_spec
    (by simp) (by intros; rfl) (by intros; rfl) r

@[expose, reducible,
  rust_trait_impl "core::iter::traits::double_ended::DoubleEndedIterator<core::ops::range::Range<@A>, @A>"]
def core.ops.range.Range.Insts.DoubleEndedIterator
  {A : Type _} (StepInst : core.iter.range.Step A) :
  core.iter.traits.double_ended.DoubleEndedIterator (core.ops.range.Range A) A
  := {
  iteratorInst := core.iter.traits.iterator.IteratorRange StepInst
  next_back := core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back StepInst
}


@[reducible,
  rust_trait_impl "core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, @A>"]
impl_def core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator
  {A : Type _} (StepInst : core.iter.range.Step A) :
  core.iter.traits.iterator.Iterator (core.ops.range.RangeInclusive A) A := {
  next :=
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next StepInst
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator StepInst)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator StepInst)
  take := core.iter.traits.iterator.Iterator.take.trait_default
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator StepInst)
}

-- ============================================================================
-- `RangeInclusive::contains`
-- ============================================================================

-- `(a..=b).contains(&x)` (the end bound is excluded once the range is exhausted).
scalar
@[step]
theorem core.ops.range.RangeInclusive.contains_'S_spec
    (r : core.ops.range.RangeInclusive «%S») (x : «%S») :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrd'S core.cmp.PartialOrd'S
      core.cmp.PartialOrd'S (SharedBorrow.mk r) (SharedBorrow.mk x)
    ⦃ b => b = decide (r.start.val ≤ x.val ∧
      (if r.exhausted then x.val < r.«end».val else x.val ≤ r.«end».val)) ⦄ := by
  unfold core.ops.range.RangeInclusive.contains
  simp [core.cmp.impls.PartialOrd'S.le, core.cmp.impls.PartialOrd'S.lt]
  split <;> (try split) <;> simp [spec_ok, *]

end Aeneas.Std
