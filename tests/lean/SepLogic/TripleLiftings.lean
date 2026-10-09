import Aeneas.Std.RawPtr
import Aeneas.Tactic.Step

namespace TripleLiftingTests

open Aeneas.Std (Result RawPtr MutRawPtr)
open Aeneas.SepLogic
open Aeneas
open Aeneas.Std.WP
open Aeneas.Std.alloc.boxed.Box (into_raw from_raw)

def totalPure (x : Nat) : Result Nat := Result.ok x
def partialPure (x : Nat) : Result Nat := Result.ok x
def totalSpatial (x : Nat) : Result Nat := Result.ok x
def partialSpatial (x : Nat) : Result Nat := Result.ok x
def legacyTotalPure (x : Nat) : Result Nat := Result.ok x
def legacyPartialPure (x : Nat) : Result Nat := Result.ok x
def legacyPair (x : Nat) : Result (Nat × Nat) := Result.ok (x, x + 1)

@[step] theorem totalPure.spec (x : Nat) : totalPure x ⦃ y => y = x ⦄ := by
  unfold totalPure
  step*

@[step] theorem partialPure.spec (x : Nat) : partialPure x ⦃ y => y = x ⦄div := by
  unfold partialPure
  step*

@[step] theorem totalSpatial.spec (x : Nat) :
    ⦃ emp ⦄ totalSpatial x ⦃ y => ⌜y = x⌝ ⦄ := by
  unfold totalSpatial
  step*

@[step] theorem partialSpatial.spec (x : Nat) :
    ⦃ emp ⦄ partialSpatial x ⦃ y => ⌜y = x⌝ ⦄div := by
  unfold partialSpatial
  step*

@[step] theorem legacyTotalPure.spec (x : Nat) :
    Aeneas.Std.WP.spec (legacyTotalPure x) (fun y => y = x) := by
  simp [legacyTotalPure]

@[step] theorem legacyPartialPure.spec (x : Nat) :
    Aeneas.Std.WP.dspec (legacyPartialPure x) (fun y => y = x) := by
  simp [legacyPartialPure]

@[step] theorem legacyPair.spec (x : Nat) :
    Aeneas.Std.WP.spec (legacyPair x)
      (Aeneas.Std.WP.uncurry' fun first second =>
        first = x ∧ second = x + 1) := by
  simp [legacyPair, Aeneas.Std.WP.spec_ok, Aeneas.Std.WP.uncurry']

run_meta do
  for (specName, arity) in
      #[(``spec, 3), (``dspec, 3), (``ispec, 4), (``dispec, 4)] do
    let some info ← Aeneas.specInfoLookup specName
      | Lean.throwError "Missing registration for {specName}"
    unless info.arity == arity do
      Lean.throwError "Incorrect arity for {specName}"
  for (specName, judgment) in
      #[(``totalPure.spec, ``spec), (``partialPure.spec, ``dspec),
        (``totalSpatial.spec, ``ispec), (``partialSpatial.spec, ``dispec)] do
    let (_, info) ← Aeneas.Step.getStepSpecFunArgsExpr (← Lean.getConstInfo specName).type
    unless info.spec_name == judgment do
      Lean.throwError "{specName} registered under the wrong judgment"

example (x : Nat) : totalPure x ⦃ y => y = x ⦄ := by step*
example (x : Nat) : totalPure x ⦃ y => y = x ⦄div := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ totalPure x ⦃ y => P ∗ ⌜y = x⌝ ⦄ := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ totalPure x ⦃ y => P ∗ ⌜y = x⌝ ⦄div := by step*

example (x : Nat) (P : IProp) :
    ⦃ P ⦄ legacyTotalPure x ⦃ y => P ∗ ⌜y = x⌝ ⦄ := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ legacyTotalPure x ⦃ y => P ∗ ⌜y = x⌝ ⦄div := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ legacyPartialPure x ⦃ y => P ∗ ⌜y = x⌝ ⦄div := by step*

def useLegacyPair (x : Nat) : Result Nat := do
  let pair ← legacyPair x
  Result.ok (pair.1 + pair.2)

example (x : Nat) :
    ⦃ emp ⦄ useLegacyPair x
        ⦃ result => ⌜result = x + (x + 1)⌝ ⦄ := by
    unfold useLegacyPair
    step as ⟨pair, hFirst, hSecond⟩
    guard_hyp hFirst : pair.1 = x
    guard_hyp hSecond : pair.2 = x + 1
    simp [hFirst, hSecond]

example (recur : Nat → Result (Nat × Nat))
    (hRecur : ∀ x,
      ⦃ emp ⦄ recur x
        ⦃ (first, second) => ⌜first = x ∧ second = x + 1⌝ ⦄)
    (x : Nat) :
    ⦃ emp ⦄ recur x
      ⦃ pair => ⌜pair.1 + pair.2 = x + (x + 1)⌝ ⦄ := by
  step with hRecur x as ⟨pair, hFirst, hSecond⟩
  guard_hyp hFirst : pair.1 = x
  guard_hyp hSecond : pair.2 = x + 1
  simp [hFirst, hSecond]

example (x : Nat) : partialPure x ⦃ y => y = x ⦄div := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ partialPure x ⦃ y => P ∗ ⌜y = x⌝ ⦄div := by step*

example (x : Nat) : totalSpatial x ⦃ y => y = x ⦄ := by step*
example (x : Nat) : totalSpatial x ⦃ y => y = x ⦄div := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ totalSpatial x ⦃ y => P ∗ ⌜y = x⌝ ⦄ := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ totalSpatial x ⦃ y => P ∗ ⌜y = x⌝ ⦄div := by step*
example (x : Nat) : partialSpatial x ⦃ y => y = x ⦄div := by step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ partialSpatial x ⦃ y => P ∗ ⌜y = x⌝ ⦄div := by step*

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
    ⦃ P ⦄ twiceTotalPure x ⦃ z => P ∗ ⌜z = x⌝ ⦄ := by
  unfold twiceTotalPure
  step*
example (x : Nat) (P : IProp) :
    ⦃ P ⦄ twicePartialPure x ⦃ z => P ∗ ⌜z = x⌝ ⦄div := by
  unfold twicePartialPure
  step*

example (x : Nat) :
    ispec emp (do
      let p ← into_raw x
      let y ← RawPtr.read p
      let _ ← from_raw p
      totalPure y) (fun z => ⌜z = x⌝) := by step*

def partialAlloc (x : Nat) := into_raw x

@[step] theorem partialAlloc.spec (x : Nat) :
    ⦃ emp ⦄ partialAlloc x ⦃ p => p ↦ x ⦄div :=
  ispec_dispec (into_raw.spec x)

example (x : Nat) :
    dispec emp (do
      let p ← partialAlloc x
      let y ← RawPtr.read p
      let _ ← from_raw p
      partialPure y) (fun z => ⌜z = x⌝) := by step*

example (m : Result Nat) (h : m ⦃ n => n = 7 ⦄) (P : IProp) :
    ⦃ P ⦄ m ⦃ n => P ∗ ⌜n = 7⌝ ⦄ := by
  step with h
example (m : Result Nat) (h : m ⦃ n => n = 7 ⦄div) (P : IProp) :
    ⦃ P ⦄ m ⦃ n => P ∗ ⌜n = 7⌝ ⦄div := by
  step with h
example (m : Result Nat) (h : ⦃ emp ⦄ m ⦃ n => ⌜n = 7⌝ ⦄) :
    m ⦃ n => n = 7 ⦄div := by
  step with h
  assumption
example (m : Result Nat) (h : ⦃ emp ⦄ m ⦃ n => ⌜n = 7⌝ ⦄div) :
    m ⦃ n => n = 7 ⦄div := by step*

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

def partialPair (x : Nat) : Result (Nat × Nat) := Result.ok (x, x + 1)

@[step] theorem partialPair.spec (x : Nat) :
    partialPair x ⦃ first second => first = x ∧ second = x + 1 ⦄div := by
  unfold partialPair
  step*

def usePartialPair (x : Nat) : Result Nat := do
  let pair ← partialPair x
  partialPure (pair.1 + pair.2)

example (x : Nat) :
    usePartialPair x ⦃ z => z = x + (x + 1) ⦄div := by
  unfold usePartialPair
  step as ⟨pair, hFirst, hSecond⟩
  guard_hyp hFirst : pair.1 = x
  guard_hyp hSecond : pair.2 = x + 1
  step*

example (x : Nat) (P : IProp) :
    ⦃ P ⦄ usePartialPair x ⦃ z => P ∗ ⌜z = x + (x + 1)⌝ ⦄div := by
  unfold usePartialPair
  step as ⟨pair⟩
  apply dispec_ipure.mpr
  rintro ⟨hFirst, hSecond⟩
  guard_hyp hFirst : pair.1 = x
  guard_hyp hSecond : pair.2 = x + 1
  step*

example (Q : Nat → Prop) :
    Lean.Order.admissible (fun m : Result Nat => m ⦃ Q ⦄div) :=
  dspec_admissible Q

def applyPure (f : Nat → Result Nat) (x : Nat) : Result Nat := f x

@[step] theorem applyPure.spec (f : Nat → Result Nat) (x : Nat) (Q : Nat → Prop)
    (hf : f x ⦃ Q ⦄) : applyPure f x ⦃ Q ⦄ := hf

example (x : Nat) :
    applyPure (fun y => Result.ok (y + 1)) x ⦃ y => y = x + 1 ⦄ := by
  apply applyPure.spec
  step*

example (x : Nat) :
    applyPure (fun y => Result.ok (y + 1)) x ⦃ y => y = x + 1 ⦄div := by
  apply spec_dspec
  apply applyPure.spec
  step*

/-- error: unsolved goals
m : Result ℕ
Q : ℕ → Prop
⊢ m ⦃ Q ⦄ -/
#guard_msgs in
example (m : Result Nat) (Q : Nat → Prop) : spec m Q := by done

/-- error: unsolved goals
m : Result ℕ
Q : ℕ → Prop
⊢ m ⦃ Q ⦄div -/
#guard_msgs in
example (m : Result Nat) (Q : Nat → Prop) : dspec m Q := by done

example (x : Nat) : partialPure x ⦃ y => y = x ⦄ := by
  fail_if_success step with partialPure.spec
  unfold partialPure
  step*

example (x : Nat) : partialSpatial x ⦃ y => y = x ⦄ := by
  fail_if_success step with partialSpatial.spec
  unfold partialSpatial
  step*

example (x : Nat) (P : IProp) :
    ⦃ P ⦄ partialPure x ⦃ y => P ∗ ⌜y = x⌝ ⦄ := by
  fail_if_success step with partialPure.spec
  unfold partialPure
  step*

example (x : Nat) (P : IProp) :
    ⦃ P ⦄ partialSpatial x ⦃ y => P ∗ ⌜y = x⌝ ⦄ := by
  fail_if_success step with partialSpatial.spec
  unfold partialSpatial
  step*

example (m : Result Nat) (p : MutRawPtr Nat)
    (hPure : m ⦃ n => n = 0 ⦄)
    (_hSpatial : ⦃ p ↦ 0 ⦄ m ⦃ n => p ↦ 0 ∗ ⌜n = 0⌝ ⦄) :
    m ⦃ n => n = 0 ⦄ := by
  fail_if_success solve | step with _hSpatial
  step with hPure
  assumption

example : totalPure 0 ⦃ n => n = 0 ⦄ := by
  fail_if_success step with (totalSpatial.spec 1)
  step with totalPure.spec
  assumption

example : True := by
  fail_if_success
    have : into_raw (0 : Nat) ⦃ _ => True ⦄ := by step*
  fail_if_success
    have : into_raw (0 : Nat) ⦃ _ => True ⦄div := by step*
  trivial

end TripleLiftingTests
