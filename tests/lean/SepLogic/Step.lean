import SepLogic.Fixtures

open Aeneas.Data.Coinductive
open SepLogic

open Aeneas
open Aeneas.SepLogic

namespace SepLogic.Tests.Step

open Aeneas.Std.WP

open Aeneas.Std (MutRawPtr RawPtr Result U32 Box)
open Aeneas.Std.MutRawPtr (write)
open Aeneas.Std.alloc.boxed.Box (into_raw from_raw)
open Aeneas.Std.RawPtr (read)


def allocAndReturn : Result (MutRawPtr U32) := do
  let p ← into_raw ⟨1#u32⟩
  pure p

example : ⦃ emp ⦄ allocAndReturn ⦃ p => p ↦ 1#u32 ∗ p.freeable 1⦄ := by
  unfold allocAndReturn
  step*

example : ⦃ emp ⦄ allocAndReturn ⦃ p => p ↦ 1#u32 ∗ p.freeable 1⦄ := by
  unfold allocAndReturn
  step
  step

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : MutRawPtr U32) : Result Nat := do
  let value ← read p
  let _ ← from_raw p
  pure (value.val + 1)

/-- `p.freeable 1` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ∗ p.freeable 1 ⦄ readFreeReturn p
      ⦃ result => ⌜opaqueStepResult result (value.val + 1)⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    step*
    done
  step* 2
  step
  simp only [opaqueStepResult]
  agrind

example : ⦃ emp ⦄ allocAndReturn
    ⦃ p => iprop(⌜opaqueStepResult 1 1⌝ ∗ p ↦ 1#u32 ∗ p.freeable 1)⦄ := by
  unfold allocAndReturn
  step* 1
  step
  guard_target = opaqueStepResult 1 1
  rfl

example (n : Nat) : ⦃ emp ⦄ Result.ok n ⦃ result => ⌜result = n⌝⦄ := by
  step

example (p : MutRawPtr U32) : ⦃ p ↦ 0#u32 ⦄ (pure () : Result Unit) ⦃ p ↦ 0#u32⦄ := by
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
  step with pure_spec

/-- `p.freeable 1` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ∗ p.freeable 1 ⦄ readFreeReturn p
      ⦃ result => ⌜result = value.val + 1⌝⦄ := by
  unfold readFreeReturn
  step*

def branchAfterRead (p : MutRawPtr U32) : Result Nat := do
  let value ← read p
  if value = 0#u32 then pure 1 else pure 2

example (p : MutRawPtr U32) (initial : U32) :
    ⦃ p ↦ initial ⦄ branchAfterRead p
      ⦃ result =>
        iprop(⌜result = if initial = 0#u32 then 1 else 2⌝ ∗ p ↦ initial)⦄ := by
  unfold branchAfterRead
  step* 1
  subst value
  by_cases h : initial = 0#u32
  · simp only [h, ↓reduceIte]
    step
  · simp only [h, ↓reduceIte]
    step

structure Ghost where
  f : Nat → Nat

inductive NeedsWitness : Prop where
  | mk : Ghost → NeedsWitness

def ghostHelper (_p : MutRawPtr U32) : Result Unit :=
  pure ()

@[step]
theorem ghostHelper.spec (p : MutRawPtr U32) (_witness : NeedsWitness) :
    ⦃ p ↦ 0#u32 ⦄ ghostHelper p ⦃ p ↦ 0#u32⦄ := by
  unfold ghostHelper
  step

def ghostCaller (p : MutRawPtr U32) : Result Unit := do
  ghostHelper p
  pure ()

example (p : MutRawPtr U32) :
    ⦃ p ↦ 0#u32 ⦄ ghostCaller p ⦃ p ↦ 0#u32⦄ := by
  unfold ghostCaller
  fail_if_success
    step*
    done
  step with ghostHelper.spec p (NeedsWitness.mk { f := id })
  step

attribute [local irreducible] opaqueStepResult in
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ read p
      ⦃ result => iprop(⌜opaqueStepResult result.val value.val⌝ ∗ p ↦ value)⦄ := by
  step as ⟨result, hResult⟩
  guard_hyp hResult : result = value
  guard_target = opaqueStepResult result.val value.val
  simp only [opaqueStepResult, hResult]

def unregisteredHelper (p : MutRawPtr U32) : Result Unit :=
  Fixtures.incr_ptr p

theorem unregisteredHelper.spec (p : MutRawPtr U32) (value : U32)
    (h : value.val + 1 ≤ U32.max) :
    ⦃ p ↦ value ⦄ unregisteredHelper p ⦃ ∃ v, ⌜v.val = value.val + 1⌝ ∗ p ↦ v⦄ := by
  unfold unregisteredHelper
  step*

def unregisteredCaller (p : MutRawPtr U32) : Result Unit := do
  unregisteredHelper p
  pure ()

example (p : MutRawPtr U32) (value : U32) (h : value.val + 1 ≤ U32.max) :
    ⦃ p ↦ value ⦄ unregisteredCaller p ⦃ ∃ v, ⌜v.val = value.val + 1⌝ ∗ p ↦ v⦄ := by
  unfold unregisteredCaller
  fail_if_success
    step*
    done
  step with unregisteredHelper.spec
  step*

end SepLogic.Tests.Step
