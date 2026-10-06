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


def allocAndReturn : Result (MutRawPtr Nat) := do
  let p ← alloc 1
  pure p

example : ⦃ emp ⦄ allocAndReturn ⦃ p => p ↦ 1⦄ := by
  unfold allocAndReturn
  step*

example : ⦃ emp ⦄ allocAndReturn ⦃ p => p ↦ 1⦄ := by
  unfold allocAndReturn
  step
  step

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : MutRawPtr Nat) : Result Nat := do
  let value ← read p
  free p
  pure (value + 1)

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    step*
    done
  step* 2
  step
  simp only [opaqueStepResult]
  agrind

example : ⦃ emp ⦄ allocAndReturn ⦃ p => iprop(⌜opaqueStepResult 1 1⌝ ∗ p ↦ 1)⦄ := by
  unfold allocAndReturn
  step* 1
  step
  guard_target = opaqueStepResult 1 1
  rfl

example (n : Nat) : ⦃ emp ⦄ Result.ok n ⦃ result => ⌜result = n⌝⦄ := by
  step

example (p : MutRawPtr Nat) : ⦃ p ↦ 0 ⦄ (pure () : Result Unit) ⦃ p ↦ 0⦄ := by
  step

def namedReturn (n : Nat) : Result Nat :=
  pure n

@[step]
theorem namedReturn.spec (n : Nat) :
    ⦃ emp ⦄ namedReturn n ⦃ result => ⌜result = n⌝⦄ := by
  unfold namedReturn
  step

example (n : Nat) : ⦃ emp ⦄ namedReturn n ⦃ result => ⌜result = n⌝⦄ := by
  step

example (n : Nat) : ⦃ emp ⦄ (pure n : Result Nat) ⦃ result => ⌜result = n⌝⦄ := by
  step with pure.spec

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃ result => ⌜result = value + 1⌝⦄ := by
  unfold readFreeReturn
  step*

def branchAfterRead (p : MutRawPtr Nat) : Result Nat := do
  let value ← read p
  if value = 0 then pure 1 else pure 2

example (p : MutRawPtr Nat) (initial : Nat) :
    ⦃ p ↦ initial ⦄ branchAfterRead p
      ⦃ result =>
        iprop(⌜result = if initial = 0 then 1 else 2⌝ ∗ p ↦ initial)⦄ := by
  unfold branchAfterRead
  step* 1
  subst value
  by_cases h : initial = 0
  · simp only [h, ↓reduceIte]
    step
  · simp only [h, ↓reduceIte]
    step

structure Ghost where
  f : Nat → Nat

inductive NeedsWitness : Prop where
  | mk : Ghost → NeedsWitness

def ghostHelper (_p : MutRawPtr Nat) : Result Unit :=
  pure ()

@[step]
theorem ghostHelper.spec (p : MutRawPtr Nat) (_witness : NeedsWitness) :
    ⦃ p ↦ 0 ⦄ ghostHelper p ⦃ p ↦ 0⦄ := by
  unfold ghostHelper
  step

def ghostCaller (p : MutRawPtr Nat) : Result Unit := do
  ghostHelper p
  pure ()

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 0 ⦄ ghostCaller p ⦃ p ↦ 0⦄ := by
  unfold ghostCaller
  fail_if_success
    step*
    done
  step with ghostHelper.spec p (NeedsWitness.mk { f := id })
  step

attribute [local irreducible] opaqueStepResult in
example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ read p
      ⦃ result => iprop(⌜opaqueStepResult result value⌝ ∗ p ↦ value)⦄ := by
  step as ⟨result, hResult⟩
  guard_hyp hResult : result = value
  guard_target = opaqueStepResult result value
  simpa only [opaqueStepResult] using hResult

def unregisteredHelper (p : MutRawPtr Nat) : Result Unit :=
  Fixtures.incr_ptr p

theorem unregisteredHelper.spec (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ unregisteredHelper p ⦃ p ↦ value + 1⦄ := by
  unfold unregisteredHelper
  step*

def unregisteredCaller (p : MutRawPtr Nat) : Result Unit := do
  unregisteredHelper p
  pure ()

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ unregisteredCaller p ⦃ p ↦ value + 1⦄ := by
  unfold unregisteredCaller
  fail_if_success
    step*
    done
  step with unregisteredHelper.spec
  step*

end SepLogic.Tests.Step
