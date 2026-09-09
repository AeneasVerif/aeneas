import Aeneas.SLPoC.MutableData.Ptr

/-!
# Registered pure and spatial judgments

Exercise the supported edges between total/partial and pure/spatial
specifications, including local contracts and framing pure calls in SL goals.
-/

namespace TripleLiftingTests

open Aeneas.Std (Result)
open Aeneas.SepLogic
open Aeneas.SepLogic.WP

def totalPure (x : Nat) : Result Nat := Result.ok x
def partialPure (x : Nat) : Result Nat := Result.ok x
def totalSpatial (x : Nat) : Result Nat := Result.ok x
def partialSpatial (x : Nat) : Result Nat := Result.ok x

@[step] theorem totalPure.spec (x : Nat) : totalPure x ⦃ y => y = x ⦄ := by
  unfold totalPure
  step

@[step] theorem partialPure.spec (x : Nat) : partialPure x ⦃ y => y = x ⦄div := by
  unfold partialPure
  step

@[step] theorem totalSpatial.spec (x : Nat) :
    ⦃ emp ⦄ totalSpatial x ⦃⇓ y => ⌜y = x⌝ ⦄ := by
  unfold totalSpatial
  step

@[step] theorem partialSpatial.spec (x : Nat) :
    ⦃ emp ⦄ partialSpatial x ⦃⇓ y => ⌜y = x⌝ ⦄div := by
  unfold partialSpatial
  step

run_meta do
  for (name, arity) in
      #[(``WP.spec, 3), (``WP.dspec, 3), (``triple, 4), (``dtriple, 4)] do
    let some info ← Aeneas.specInfoLookup name
      | throwError "Missing registration for {name}"
    unless info.arity == arity do
      throwError "Incorrect arity for {name}"
  for (name, judgment) in
      #[(``totalPure.spec, ``WP.spec), (``partialPure.spec, ``WP.dspec),
        (``totalSpatial.spec, ``triple), (``partialSpatial.spec, ``dtriple)] do
    let (_, info) ← Aeneas.Step.getStepSpecFunArgsExpr (← Lean.getConstInfo name).type
    unless info.spec_name == judgment do
      throwError "{name} registered under the wrong judgment"

/-! Total pure specifications work in all four judgments. -/

example (x : Nat) : totalPure x ⦃ y => y = x ⦄ := by step
example (x : Nat) : totalPure x ⦃ y => y = x ⦄div := by step
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ totalPure x ⦃⇓ y => P ∗ ⌜y = x⌝ ⦄ := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ totalPure x ⦃⇓ y => P ∗ ⌜y = x⌝ ⦄div := by step*

/-! Partial pure specifications work only in partial judgments. -/

example (x : Nat) : partialPure x ⦃ y => y = x ⦄div := by step
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ partialPure x ⦃⇓ y => P ∗ ⌜y = x⌝ ⦄div := by step*

/-! SL specifications at `emp` with pure postconditions also work in pure goals. -/

example (x : Nat) : totalSpatial x ⦃ y => y = x ⦄ := by step
example (x : Nat) : totalSpatial x ⦃ y => y = x ⦄div := by step
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ totalSpatial x ⦃⇓ y => P ∗ ⌜y = x⌝ ⦄ := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ totalSpatial x ⦃⇓ y => P ∗ ⌜y = x⌝ ⦄div := by step*
example (x : Nat) : partialSpatial x ⦃ y => y = x ⦄div := by step
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ partialSpatial x ⦃⇓ y => P ∗ ⌜y = x⌝ ⦄div := by step*

/-! Bind rules preserve the judgment of the continuation. -/

example (x : Nat) :
    (do let y ← totalPure x; totalPure y) ⦃ z => z = x ⦄ := by step*
example (x : Nat) :
    (do let y ← totalPure x; partialPure y) ⦃ z => z = x ⦄div := by step*
example (x : Nat) :
    (do let y ← partialPure x; totalSpatial y) ⦃ z => z = x ⦄div := by step*
example (x : Nat) :
    (do let y ← totalSpatial x; totalPure y) ⦃ z => z = x ⦄ := by step*
example (x : Nat) :
    (do let y ← totalSpatial x; partialPure y) ⦃ z => z = x ⦄div := by step*
example (x : Nat) :
    (do let y ← partialSpatial x; totalPure y) ⦃ z => z = x ⦄div := by step*

def twiceTotalPure (x : Nat) : Result Nat := do
  let y ← totalPure x
  totalPure y

def twicePartialPure (x : Nat) : Result Nat := do
  let y ← partialPure x
  totalPure y

example (x : Nat) (P : IProp) :
    ⦃ P ⦄ twiceTotalPure x ⦃⇓ z => P ∗ ⌜z = x⌝ ⦄ := by
  unfold twiceTotalPure
  step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ twicePartialPure x ⦃⇓ z => P ∗ ⌜z = x⌝ ⦄div := by
  unfold twicePartialPure
  step*

/-! SL goals carry resources through allocating callees, including callees
that have only a partial specification. -/

example (x : Nat) :
    triple emp (do
      let p ← alloc x
      let y ← read p
      free p
      totalPure y) (fun z => ⌜z = x⌝) := by step*

def partialAlloc (x : Nat) := alloc x

@[step] theorem partialAlloc.spec (x : Nat) :
    ⦃ emp ⦄ partialAlloc x ⦃⇓ p => p ↦ x ⦄div :=
  triple_dtriple (alloc.spec x)

example (x : Nat) :
    dtriple emp (do
      let p ← partialAlloc x
      let y ← read p
      free p
      partialPure y) (fun z => ⌜z = x⌝) := by step*

/-! Local contracts and explicit theorem selection use the same liftings. -/

example (m : Result Nat) (h : m ⦃ n => n = 7 ⦄) (P : IProp) :
    ⦃ P ⦄ m ⦃⇓ n => P ∗ ⌜n = 7⌝ ⦄ := by
  step with h
  iframe
example (m : Result Nat) (h : m ⦃ n => n = 7 ⦄div) (P : IProp) :
    ⦃ P ⦄ m ⦃⇓ n => P ∗ ⌜n = 7⌝ ⦄div := by
  step with h
  iframe
example (m : Result Nat) (h : ⦃ emp ⦄ m ⦃⇓ n => ⌜n = 7⌝ ⦄) :
    m ⦃ n => n = 7 ⦄div := by step with h
example (m : Result Nat) (h : ⦃ emp ⦄ m ⦃⇓ n => ⌜n = 7⌝ ⦄div) :
    m ⦃ n => n = 7 ⦄div := by step

universe u v

example {α : Type u} {β : Type v} (m : Result α) (next : α → Result β)
    (P : α → Prop) (Q : β → Prop)
    (hm : m ⦃ P ⦄) (hn : ∀ x, P x → next x ⦃ Q ⦄) :
    Aeneas.Std.bind m next ⦃ Q ⦄ := by
  step with hm
  step with hn
  assumption

example {α : Type u} {β : Type v} (m : Result α) (next : α → Result β)
    (P : α → Prop) (Q : β → Prop)
    (hm : m ⦃ P ⦄div) (hn : ∀ x, P x → next x ⦃ Q ⦄div) :
    Aeneas.Std.bind m next ⦃ Q ⦄div := by step*

/-! Lifting tuple postconditions must preserve both components and their
pure hypotheses before the continuation is introduced. -/

def partialPair (x : Nat) : Result (Nat × Nat) := Result.ok (x, x + 1)

@[step] theorem partialPair.spec (x : Nat) :
    partialPair x ⦃ first second => first = x ∧ second = x + 1 ⦄div := by
  unfold partialPair
  step

def usePartialPair (x : Nat) : Result Nat := do
  let pair ← partialPair x
  partialPure (pair.1 + pair.2)

example (x : Nat) :
    usePartialPair x ⦃ z => z = x + (x + 1) ⦄div := by
  unfold usePartialPair
  step as ⟨first, second, hFirst, hSecond⟩
  guard_hyp hFirst : first = x
  guard_hyp hSecond : second = x + 1
  step*

example (x : Nat) (P : IProp) :
    ⦃ P ⦄ usePartialPair x ⦃⇓ z => P ∗ ⌜z = x + (x + 1)⌝ ⦄div := by
  unfold usePartialPair
  step as ⟨first, second, hFirst, hSecond⟩
  guard_hyp hFirst : first = x
  guard_hyp hSecond : second = x + 1
  step*

example (Q : Nat → Prop) :
    Lean.Order.admissible (fun m : Result Nat => m ⦃ Q ⦄div) :=
  WP.dspec_admissible Q

def applyPure (f : Nat → Result Nat) (x : Nat) : Result Nat := f x

@[step] theorem applyPure.spec (f : Nat → Result Nat) (x : Nat) (Q : Nat → Prop)
    (hf : f x ⦃ Q ⦄) : applyPure f x ⦃ Q ⦄ := hf

example (x : Nat) :
    applyPure (fun y => Result.ok (y + 1)) x ⦃ y => y = x + 1 ⦄ := by
  step* +inferPost

example (x : Nat) :
    applyPure (fun y => Result.ok (y + 1)) x ⦃ y => y = x + 1 ⦄div := by
  step* +inferPost

/-- error: unsolved goals
m : Result ℕ
Q : ℕ → Prop
⊢ m ⦃ Q ⦄ -/
#guard_msgs in
example (m : Result Nat) (Q : Nat → Prop) : WP.spec m Q := by done

/-- error: unsolved goals
m : Result ℕ
Q : ℕ → Prop
⊢ m ⦃ Q ⦄div -/
#guard_msgs in
example (m : Result Nat) (Q : Nat → Prop) : WP.dspec m Q := by done

/-! No lifting may upgrade partial correctness or turn a spatial contract into
a pure one by discarding its owned resources. -/

example (x : Nat) : partialPure x ⦃ y => y = x ⦄ := by
  fail_if_success step with partialPure.spec
  unfold partialPure
  step*

example (x : Nat) : partialSpatial x ⦃ y => y = x ⦄ := by
  fail_if_success step with partialSpatial.spec
  unfold partialSpatial
  step

example (x : Nat) (P : IProp) :
    ⦃ P ⦄ partialPure x ⦃⇓ y => P ∗ ⌜y = x⌝ ⦄ := by
  fail_if_success step with partialPure.spec
  unfold partialPure
  step*

example (x : Nat) (P : IProp) :
    ⦃ P ⦄ partialSpatial x ⦃⇓ y => P ∗ ⌜y = x⌝ ⦄ := by
  fail_if_success step with partialSpatial.spec
  unfold partialSpatial
  step*

example (m : Result Nat) (p : Ptr Nat)
    (hPure : m ⦃ n => n = 0 ⦄)
    (_hSpatial : ⦃ p ↦ 0 ⦄ m ⦃⇓ n => p ↦ 0 ∗ ⌜n = 0⌝ ⦄) :
    m ⦃ n => n = 0 ⦄ := by
  fail_if_success solve | step with _hSpatial
  step with hPure

example : totalPure 0 ⦃ n => n = 0 ⦄ := by
  fail_if_success step with (totalSpatial.spec 1)
  step with totalPure.spec

example : True := by
  fail_if_success
    have : alloc (0 : Nat) ⦃ _ => True ⦄ := by step
  fail_if_success
    have : alloc (0 : Nat) ⦃ _ => True ⦄div := by step
  trivial

end TripleLiftingTests
