import Aeneas.SLPoC.Tests.Examples.Basic

open Aeneas.Data.Coinductive

namespace Aeneas.SLPoC.Tests.Step

open Aeneas.Std (Result)


/-! ## A result-dependent spatial postcondition

This is the small version of the terminal `step` proofs in `PulseLinkedList`,
`IrisTutorial`, and `VerusBitmap`. Going through `pure.spec` leaves a
postcondition wand stated in terms of the abstract result of the specification;
`entails_postWand_pure_eq` collapses it, which restates the obligation about the
returned value and makes it framable — so an unbounded `step*` closes this on
its own.
-/

def allocAndReturn : Result (Ptr Nat) := do
  let p ← alloc 1
  pure p

example : ⦃ emp ⦄ allocAndReturn ⦃⇓ p => p ↦ 1⦄ := by
  unfold allocAndReturn
  step*

/-- The same goal reached one step at a time. -/
example : ⦃ emp ⦄ allocAndReturn ⦃⇓ p => p ↦ 1⦄ := by
  unfold allocAndReturn
  step*

/-! ## Manual work on the terminal entailment

This is the reason for the bounds before the terminal `step` in `UnitTest`,
`AsterinasIntrusiveFrameList`, and several data-structure examples. An
unbounded `step*` reaches an entailment that only becomes frameable after
the user unfolds or simplifies the postcondition.
-/

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : Ptr Nat) : Result Nat := do
  let value ← read p
  free p
  pure (value + 1)

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    step*
    done
  step* 2
  step
  simp only [opaqueStepResult]
  iframe

/-! ## The terminal return

`step` uses the registered `pure.spec` and leaves its ramified-frame entailment
as the mono goal. The simplification passes collapse its result-equality wand,
after which an explicit `iframe` closes routine terminal goals. `step*` runs
that registered final discharger itself.
-/

/-- What `iframe` cannot close is left as the goal, stated about the returned
value: the assertion the entailment starts from and the one its postcondition
asks for are the *same*, which is what `pure_sep_intro` needs here. -/
example : ⦃ emp ⦄ allocAndReturn ⦃⇓ p => iprop(⌜opaqueStepResult 1 1⌝ ∗ p ↦ 1)⦄ := by
  unfold allocAndReturn
  step* 1
  step
  exact pure_sep_intro _ rfl

/-- `Result.ok`, the constructor `pure` unfolds to, is a terminal return too. -/
example (n : Nat) : ⦃ emp ⦄ Result.ok n ⦃⇓ result => ⌜result = n⌝⦄ := by
  step
  iframe

/-- A `Unit` result is no different. -/
example (p : Ptr Nat) : ⦃ p ↦ 0 ⦄ (pure () : Result Unit) ⦃⇓ p ↦ 0⦄ := by
  step
  iframe

def namedReturn (n : Nat) : Result Nat :=
  pure n

@[step]
theorem namedReturn.spec (n : Nat) :
    ⦃ emp ⦄ namedReturn n ⦃⇓ result => ⌜result = n⌝⦄ := by
  unfold namedReturn
  step
  iframe

/-- A named pure wrapper is not a *syntactic* return: the terminal rule does not
unfold it, so the step goes through its registered specification. -/
example (n : Nat) : ⦃ emp ⦄ namedReturn n ⦃⇓ result => ⌜result = n⌝⦄ := by
  step
  iframe

/-- An explicitly named specification wins over the terminal rule. -/
example (n : Nat) : ⦃ emp ⦄ (pure n : Result Nat) ⦃⇓ result => ⌜result = n⌝⦄ := by
  step with pure.spec
  iframe

/-! ## An unbounded star consumes the whole goal

The finite sequence in `UnitTest` cannot be replaced in-place by `step*`:
the star also proves the terminal entailment, so the following tactic fails
with no goals.
-/

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readFreeReturn
  step*

/-! ## The proof must branch before stepping further

This is the small version of bounded stars followed by `split` or `by_cases`.
An unbounded star performs the branch itself, so it cannot replace the bounded
step in-place when the following proof needs to control that branch.
-/

def branchAfterRead (p : Ptr Nat) : Result Nat := do
  let value ← read p
  if value = 0 then pure 1 else pure 2

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ branchAfterRead p
      ⦃⇓ result =>
        iprop(⌜result = if value = 0 then 1 else 2⌝ ∗ p ↦ value)⦄ := by
  unfold branchAfterRead
  fail_if_success
    step*
    by_cases h : value = 0
  step* 1
  by_cases h : value = 0 <;> simp only [h, ↓reduceIte] <;> step <;> iframe

/-! ## A specification argument is not inferable

This minimizes the recursive proofs in `PulseLinkedList`, `IrisTutorial`,
`VerusBitmap`, and `VerusPageTable` where the specification is registered but
some ghost arguments still have to be supplied explicitly.
-/

structure Ghost where
  f : Nat → Nat

inductive NeedsWitness : Prop where
  | mk : Ghost → NeedsWitness

def ghostHelper (_p : Ptr Nat) : Result Unit :=
  pure ()

@[step]
theorem ghostHelper.spec (p : Ptr Nat) (_witness : NeedsWitness) :
    ⦃ p ↦ 0 ⦄ ghostHelper p ⦃⇓ p ↦ 0⦄ := by
  unfold ghostHelper
  step
  iframe

def ghostCaller (p : Ptr Nat) : Result Unit := do
  ghostHelper p
  pure ()

example (p : Ptr Nat) :
    ⦃ p ↦ 0 ⦄ ghostCaller p ⦃⇓ p ↦ 0⦄ := by
  unfold ghostCaller
  fail_if_success
    step*
    done
  step with ghostHelper.spec p (NeedsWitness.mk { f := id })
  step
  iframe

/-! ## A failed discharge leaves inference metavariables unsolved -/

/-- `iframe` can infer the value argument of `read.spec` by matching the
points-to assertions, but then fails to prove the opaque pure fact. Its failure
rolls back that assignment, so `step` leaves the `Nat` metavariable as the first
goal. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ read p
      ⦃⇓ result => iprop(⌜opaqueStepResult result value⌝ ∗ p ↦ value)⦄ := by
  step
  · guard_target = Nat
    exact value
  · simp only [opaqueStepResult]
    iframe

/-! ## The required specification is not registered

This minimizes the explicit steps in `UnitTest`,
`CreusotListReversalLasso`, and `VerusPageTable`. No length of `step*` can
select a theorem absent from the step database.
-/

def unregisteredHelper (p : Ptr Nat) : Result Unit :=
  Examples.incr_ptr p

@[step]
theorem unregisteredHelper.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ unregisteredHelper p ⦃⇓ p ↦ value + 1⦄ := by
  unfold unregisteredHelper
  step*

def unregisteredCaller (p : Ptr Nat) : Result Unit := do
  unregisteredHelper p
  pure ()

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ unregisteredCaller p ⦃⇓ p ↦ value + 1⦄ := by
  unfold unregisteredCaller
  step*

end Aeneas.SLPoC.Tests.Step
