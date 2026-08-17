import Aeneas.SLPoC.Examples.Basic

namespace Aeneas.SLPoC.Tests.Step

open scoped SepLogic

/-! ## A result-dependent spatial postcondition

This is the small version of the bounded `sl_step*; sl_pure` proofs in
`PulseLinkedList`, `IrisTutorial`, and `VerusBitmap`. `sl_step` uses
`pure.spec`, whose abstract result leaves a postcondition wand that
`sl_frame` cannot cancel.
-/

def allocAndReturn : St (Ptr Nat) := do
  let p ← alloc 1
  pure p

example : ⦃ emp ⦄ allocAndReturn ⦃⇓ p => p ↦ 1⦄ := by
  unfold allocAndReturn
  fail_if_success
    sl_step*
    done
  sl_step* 1
  fail_if_success sl_step
  sl_pure
  sl_frame

/-! ## Manual work on the terminal entailment

This is the reason for the bounds before `sl_pure` in `UnitTest`,
`AsterinasIntrusiveFrameList`, and several data-structure examples. An
unbounded `sl_step*` reaches an entailment that only becomes frameable after
the user unfolds or simplifies the postcondition.
-/

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : Ptr Nat) : St Nat := do
  let value ← read p
  free p
  pure (value + 1)

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    sl_step*
    done
  sl_step* 2
  fail_if_success sl_step
  sl_pure
  simp only [opaqueStepResult]
  sl_frame

/-! ## An unbounded star consumes the whole goal

The finite sequence in `UnitTest` cannot be replaced in-place by `sl_step*`:
the star also proves the terminal entailment, so the following tactic fails
with no goals.
-/

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readFreeReturn
  sl_step*

/-! ## The proof must branch before stepping further

This is the small version of bounded stars followed by `split` or `by_cases`.
An unbounded star performs the branch itself, so it cannot replace the bounded
step in-place when the following proof needs to control that branch.
-/

def branchAfterRead (p : Ptr Nat) : St Nat := do
  let value ← read p
  if value = 0 then pure 1 else pure 2

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ branchAfterRead p
      ⦃⇓ result =>
        iprop(⌜result = if value = 0 then 1 else 2⌝ ∗ p ↦ value)⦄ := by
  unfold branchAfterRead
  fail_if_success
    sl_step*
    by_cases h : value = 0
  sl_step* 1
  by_cases h : value = 0 <;> simp only [h, ↓reduceIte] <;> sl_step

/-! ## A specification argument is not inferable

This minimizes the recursive proofs in `PulseLinkedList`, `IrisTutorial`,
`VerusBitmap`, and `VerusPageTable` where the specification is registered but
some ghost arguments still have to be supplied explicitly.
-/

structure Ghost where
  f : Nat → Nat

inductive NeedsWitness : Prop where
  | mk : Ghost → NeedsWitness

def ghostHelper (_p : Ptr Nat) : St Unit :=
  pure ()

@[step]
theorem ghostHelper.spec (p : Ptr Nat) (_witness : NeedsWitness) :
    ⦃ p ↦ 0 ⦄ ghostHelper p ⦃⇓ p ↦ 0⦄ := by
  unfold ghostHelper
  sl_pure
  sl_frame

def ghostCaller (p : Ptr Nat) : St Unit := do
  ghostHelper p
  pure ()

example (p : Ptr Nat) :
    ⦃ p ↦ 0 ⦄ ghostCaller p ⦃⇓ p ↦ 0⦄ := by
  unfold ghostCaller
  fail_if_success
    sl_step*
    done
  sl_step with ghostHelper.spec p (NeedsWitness.mk { f := id })
  sl_pure
  sl_frame

/-! ## The required specification is not registered

This minimizes the explicit steps in `UnitTest`,
`CreusotListReversalLasso`, and `VerusPageTable`. No length of `sl_step*` can
select a theorem absent from the step database.
-/

def unregisteredHelper (p : Ptr Nat) : St Unit :=
  Examples.incr_ptr p

@[step]
theorem unregisteredHelper.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ unregisteredHelper p ⦃⇓ p ↦ value + 1⦄ := by
  unfold unregisteredHelper
  sl_step*

def unregisteredCaller (p : Ptr Nat) : St Unit := do
  unregisteredHelper p
  pure ()

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ unregisteredCaller p ⦃⇓ p ↦ value + 1⦄ := by
  unfold unregisteredCaller
  sl_step*

end Aeneas.SLPoC.Tests.Step
