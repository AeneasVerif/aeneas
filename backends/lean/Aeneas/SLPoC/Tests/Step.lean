import Aeneas.SLPoC.Examples.Basic

namespace Aeneas.SLPoC.Tests.Step

open scoped SepLogic

/-! ## A result-dependent spatial postcondition

This is the small version of the bounded `sl_step*; sl_step` proofs in
`PulseLinkedList`, `IrisTutorial`, and `VerusBitmap`. Going through
`pure.spec` would leave a postcondition wand stated in terms of the abstract
result of the specification, which `sl_frame` cannot cancel; `sl_step` takes
the terminal rule directly and states the obligation about the returned value.
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
  sl_step

/-! ## Manual work on the terminal entailment

This is the reason for the bounds before the terminal `sl_step` in `UnitTest`,
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
  sl_step
  simp only [opaqueStepResult]
  sl_frame

/-! ## The terminal return

`sl_step` takes the mono case of a syntactic terminal return directly, through
`triple_pure`, and hands the resulting `P ⊢ Q v` to `sl_frame`.  Going through
the registered `pure.spec` instead would state that obligation about the
*abstract* result of the specification — `P ⊢ emp ∗ ((fun result => ⌜result =
v⌝) -∗+ Q)` — and cancelling that wand needs the pure fact it introduces to be
substituted back into the spatial part, which `sl_frame` does not do.
-/

/-- What `sl_frame` cannot close is left as the goal, stated about the returned
value: the assertion the entailment starts from and the one its postcondition
asks for are the *same*, which is what `hpure_hstar_intro` needs here. -/
example : ⦃ emp ⦄ allocAndReturn ⦃⇓ p => iprop(⌜opaqueStepResult 1 1⌝ ∗ p ↦ 1)⦄ := by
  unfold allocAndReturn
  sl_step* 1
  sl_step
  exact hpure_hstar_intro _ rfl

/-- `FFree.ok`, the constructor `pure` unfolds to, is a terminal return too. -/
example (n : Nat) : ⦃ emp ⦄ (FFree.ok n : St Nat) ⦃⇓ result => ⌜result = n⌝⦄ := by
  sl_step

/-- A `Unit` result is no different. -/
example (p : Ptr Nat) : ⦃ p ↦ 0 ⦄ (pure () : St Unit) ⦃⇓ p ↦ 0⦄ := by
  sl_step

def namedReturn (n : Nat) : St Nat :=
  pure n

@[step]
theorem namedReturn.spec (n : Nat) :
    ⦃ emp ⦄ namedReturn n ⦃⇓ result => ⌜result = n⌝⦄ := by
  unfold namedReturn
  sl_step

/-- A named pure wrapper is not a *syntactic* return: the terminal rule does not
unfold it, so the step goes through its registered specification. -/
example (n : Nat) : ⦃ emp ⦄ namedReturn n ⦃⇓ result => ⌜result = n⌝⦄ := by
  sl_step

/-- An explicitly named specification wins over the terminal rule. -/
example (n : Nat) : ⦃ emp ⦄ (pure n : St Nat) ⦃⇓ result => ⌜result = n⌝⦄ := by
  sl_step with pure.spec

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
  sl_step

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
  sl_step

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
