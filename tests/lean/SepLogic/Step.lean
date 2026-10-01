import SepLogic.Fixtures

open Aeneas.Data.Coinductive
open SepLogic

open Aeneas
open Aeneas.SepLogic

namespace SepLogic.Tests.Step

open Aeneas.Std.WP

open Aeneas.Std (MutRawPtr RawPtr Result)
open Aeneas.Std.MutRawPtr (alloc free write)
open Aeneas.Std.RawPtr (read)


/-! ## A result-dependent spatial postcondition

This is the small version of the terminal `step` proofs in `PulseLinkedList`,
`IrisTutorial`, and `VerusBitmap`. Going through `pure.spec` leaves a
postcondition wand stated in terms of the abstract result of the specification;
`entails_postWand_pure_eq` collapses it, which restates the obligation about the
returned value and makes it framable — so an unbounded `step*` closes this on
its own.
-/

def allocAndReturn : Result (MutRawPtr Nat) := do
  let p ← alloc 1
  pure p

example : ⦃ emp ⦄ allocAndReturn ⦃⇓ p => p ↦ 1⦄ := by
  unfold allocAndReturn
  step*

/-- The same goal reached one step at a time. -/
example : ⦃ emp ⦄ allocAndReturn ⦃⇓ p => p ↦ 1⦄ := by
  unfold allocAndReturn
  step
  step

/-! ## Manual work on the terminal entailment

This is the reason for the bounds before the terminal `step` in `UnitTest`,
`AsterinasIntrusiveFrameList`, and several data-structure examples. An
unbounded `step*` reaches an entailment that only becomes frameable after
the user unfolds or simplifies the postcondition.
-/

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : MutRawPtr Nat) : Result Nat := do
  let value ← read p
  free p
  pure (value + 1)

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    step*
    done
  step* 2
  step
  simp only [opaqueStepResult]
  agrind

/-! ## The terminal return

`step` uses the registered `pure.spec`. Its introduction hooks simplify the
ramified-frame entailment, closing routine spatial goals and leaving any
unresolved pure facts for the caller.
-/

/-- Matching spatial resources are cancelled, leaving the unresolved pure fact. -/
example : ⦃ emp ⦄ allocAndReturn ⦃⇓ p => iprop(⌜opaqueStepResult 1 1⌝ ∗ p ↦ 1)⦄ := by
  unfold allocAndReturn
  step* 1
  step
  guard_target = opaqueStepResult 1 1
  rfl

/-- `Result.ok`, the constructor `pure` unfolds to, is a terminal return too. -/
example (n : Nat) : ⦃ emp ⦄ Result.ok n ⦃⇓ result => ⌜result = n⌝⦄ := by
  step

/-- A `Unit` result is no different. -/
example (p : MutRawPtr Nat) : ⦃ p ↦ 0 ⦄ (pure () : Result Unit) ⦃⇓ p ↦ 0⦄ := by
  step

def namedReturn (n : Nat) : Result Nat :=
  pure n

@[step]
theorem namedReturn.spec (n : Nat) :
    ⦃ emp ⦄ namedReturn n ⦃⇓ result => ⌜result = n⌝⦄ := by
  unfold namedReturn
  step

/-- A named pure wrapper is not a *syntactic* return: the terminal rule does not
unfold it, so the step goes through its registered specification. -/
example (n : Nat) : ⦃ emp ⦄ namedReturn n ⦃⇓ result => ⌜result = n⌝⦄ := by
  step

/-- An explicitly named specification wins over the terminal rule. -/
example (n : Nat) : ⦃ emp ⦄ (pure n : Result Nat) ⦃⇓ result => ⌜result = n⌝⦄ := by
  step with pure.spec

/-! ## An unbounded star consumes the whole goal

The finite sequence in `UnitTest` cannot be replaced in-place by `step*`:
the star also proves the terminal entailment, so the following tactic fails
with no goals.
-/

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readFreeReturn
  step*

/-! ## The proof must branch before stepping further

This is the small version of bounded stars followed by `split` or `by_cases`.
A bounded star leaves the branch for the caller, who relates the read value
to the original value before choosing a branch.
-/

def branchAfterRead (p : MutRawPtr Nat) : Result Nat := do
  let value ← read p
  if value = 0 then pure 1 else pure 2

example (p : MutRawPtr Nat) (initial : Nat) :
    ⦃ p ↦ initial ⦄ branchAfterRead p
      ⦃⇓ result =>
        iprop(⌜result = if initial = 0 then 1 else 2⌝ ∗ p ↦ initial)⦄ := by
  unfold branchAfterRead
  step* 1
  subst value
  by_cases h : initial = 0
  · simp only [h, ↓reduceIte]
    step
  · simp only [h, ↓reduceIte]
    step

/-! ## A specification argument is not inferable

This minimizes the recursive proofs in `PulseLinkedList`, `IrisTutorial`,
`VerusBitmap`, and `VerusPageTable` where the specification is registered but
some ghost arguments still have to be supplied explicitly.
-/

structure Ghost where
  f : Nat → Nat

inductive NeedsWitness : Prop where
  | mk : Ghost → NeedsWitness

def ghostHelper (_p : MutRawPtr Nat) : Result Unit :=
  pure ()

@[step]
theorem ghostHelper.spec (p : MutRawPtr Nat) (_witness : NeedsWitness) :
    ⦃ p ↦ 0 ⦄ ghostHelper p ⦃⇓ p ↦ 0⦄ := by
  unfold ghostHelper
  step

def ghostCaller (p : MutRawPtr Nat) : Result Unit := do
  ghostHelper p
  pure ()

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 0 ⦄ ghostCaller p ⦃⇓ p ↦ 0⦄ := by
  unfold ghostCaller
  fail_if_success
    step*
    done
  step with ghostHelper.spec p (NeedsWitness.mk { f := id })
  step

/-! ## Inference survives an unresolved pure postcondition -/

attribute [local irreducible] opaqueStepResult in
/-- Matching the points-to assertions infers the value argument of `read.spec`.
The remaining pure fact does not roll back that inference. Keep the predicate
irreducible here so automatic discharge cannot close it by reflexivity. -/
example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ read p
      ⦃⇓ result => iprop(⌜opaqueStepResult result value⌝ ∗ p ↦ value)⦄ := by
  step as ⟨result, hResult⟩
  guard_hyp hResult : result = value
  guard_target = opaqueStepResult result value
  simpa only [opaqueStepResult] using hResult

/-! ## The required specification is not registered

This minimizes the explicit steps in `UnitTest`,
`CreusotListReversalLasso`, and `VerusPageTable`. No length of `step*` can
select a theorem absent from the step database.
-/

def unregisteredHelper (p : MutRawPtr Nat) : Result Unit :=
  Fixtures.incr_ptr p

theorem unregisteredHelper.spec (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ unregisteredHelper p ⦃⇓ p ↦ value + 1⦄ := by
  unfold unregisteredHelper
  step*

def unregisteredCaller (p : MutRawPtr Nat) : Result Unit := do
  unregisteredHelper p
  pure ()

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ unregisteredCaller p ⦃⇓ p ↦ value + 1⦄ := by
  unfold unregisteredCaller
  fail_if_success
    step*
    done
  step with unregisteredHelper.spec
  step*

end SepLogic.Tests.Step
