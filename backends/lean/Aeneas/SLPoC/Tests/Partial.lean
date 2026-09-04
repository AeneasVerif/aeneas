import Aeneas.SLPoC.Tests.Examples.Basic

/-!
# Partial correctness

`Aeneas.SepLogic.ST` states the divergence-tolerant triple `dtriple`, written
`⦃P⦄ m ⦃⇓ x => Q⦄div`.  These are the tests that it proves what a total triple
proves of a program that stops, that the automation drives it — through the
lifting of the total specifications, which are the ones `@[step]` collects — and
that it proves what a total triple cannot: a loop that never leaves.
-/

namespace Aeneas.SepLogic

open Aeneas.Data.Coinductive

open Aeneas.Std (Heap Result loop)

/-! ## The automation drives a partial goal

`step` and `step*` work on `dtriple` exactly as on `triple`: the `@[step]`
specifications state *total* correctness, and `triple_dtriple` lifts each of
them where it is applied, as `Aeneas.Std.WP.spec_dspec` does for `Result`. -/

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ Examples.incr_ptr p ⦃⇓ p ↦ value + 1⦄div := by
  step*

example (value : Nat) :
    (Examples.incr_borrow value) ⦃⇓ result => result = value + 1⦄div := by
  step*

example (x : Nat) :
    (do
      let y ← Examples.add1 x
      Examples.add1 y) ⦃⇓ y => y = x + 2⦄div := by
  step*

/-- A program written out in full, allocation to deallocation, proved partially
correct with no more work than it takes to prove it totally correct. -/
def roundTripPartial : Result Nat := do
  let p ← alloc (1 : Nat)
  let value ← read p
  update p (value + 41)
  let result ← read p
  free p
  pure result

theorem roundTripPartial.spec : (roundTripPartial) ⦃⇓ result => result = 42⦄div := by
  unfold roundTripPartial
  step*

/-- And a total proof is a partial one, so it need not be redone. -/
example : ⦃ emp ⦄ Examples.incr_borrow 1 ⦃⇓ result => ⌜result = 2⌝⦄div :=
  triple_dtriple (Examples.incr_borrow.spec 1)

/-- The proof-mode tactics have partial counterparts: `dwp_pures` for a terminal
`pure`, `dwp_apply` for a terminal call through the ramified frame rule, and
`dwp_mono` to weaken a triple already proved. -/
example (p : Ptr Nat) : ⦃ p ↦ 1 ⦄ (pure 5 : Result Nat) ⦃⇓ v => ⌜v = 5⌝ ∗ p ↦ 1⦄div := by
  dwp_pures
  isimpl

example (p q : Ptr Nat) (x : Nat) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9) ⦄ Examples.incr_ptr p ⦃⇓ iprop(q ↦ 9 ∗ p ↦ (x + 1))⦄div := by
  dwp_apply (triple_dtriple (Examples.incr_ptr.spec p x))

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ Examples.incr_ptr p ⦃⇓ emp⦄div := by
  dwp_mono (triple_dtriple (Examples.incr_ptr.spec p value))

/-! ## What partial correctness still owes

Divergence is permitted; being stuck is not, and a terminating run still
establishes the postcondition. -/

example (p : Ptr Nat) (value : Nat) (h : Heap) (hPre : (p ↦ value) h)
    (result : Unit) (h' : Heap)
    (hEval : Evaluates (Examples.incr_ptr p) h result h') :
    (p ↦ value + 1) h' :=
  dtriple_evaluates (triple_dtriple (Examples.incr_ptr.spec p value)) hPre hEval

section

unseal Result

/-- Being stuck, on the other hand, is not permitted: a read through a pointer
nothing owns has no partial triple either, since `PartialSpec` proves the guard
of every event it reaches exactly as `TotalSpec` does. -/
example (p : Ptr Nat) (Q : IPost Nat) : ¬ dtriple emp (read p) Q := by
  intro hTriple
  have hSpec : dspec (read p) Q ∅ := dtriple_apply hTriple trivial
  simp only [read, Result.guardedModify] at hSpec
  obtain ⟨hReadable, -⟩ := PartialSpec.vis_view hSpec
  exact Ptr.not_contains_empty p hReadable.contains

end

/-! ## What only partial correctness proves

`Result.div` — the tree of an unproductive recursion — satisfies every partial
triple and no total one at all. -/

example (Q : IPost Nat) : dtriple emp (Result.div : Result Nat) Q :=
  dtriple_div

example (Q : IPost Nat) : ¬ triple emp (Result.div : Result Nat) Q := fun hTriple =>
  spec_div Q Heap.empty (triple_apply hTriple trivial)

/-! ## A loop that never leaves

`partial_fixpoint` asks for an admissible invariant the recursive body restores
and for nothing else: no measure, no variant, no proof that the loop is ever
left. The loop below never is, and it owns the cell it increments for as long
as it runs. -/

/-- Increment the cell `p` for ever. -/
def incrForever (p : Ptr Nat) : Result Empty := do
  let value ← read p
  update p (value + 1)
  incrForever p
partial_fixpoint

theorem incrForever.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incrForever p ⦃⇓ emp⦄div := by
  revert value
  refine incrForever.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃⇓ emp⦄div)
    (dtriple_admissible_forall (fun v : Nat => iprop(p ↦ v)) (fun _ _ => emp)) ?_
  intro loop hLoop v
  step*

/-- The same rule proves a loop that does stop.  Partial correctness claims only
that *if* the countdown leaves, the cell it owns is zero — and proving that much
needs the invariant alone, where a total triple would also need the measure that
`value` decreases. -/
def countdown (p : Ptr Nat) : Result Unit := do
  let value ← read p
  if value = 0 then
    pure ()
  else do
    update p (value - 1)
    countdown p
partial_fixpoint

theorem countdown.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ countdown p ⦃⇓ p ↦ 0⦄div := by
  revert value
  refine countdown.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃⇓ p ↦ 0⦄div)
    (dtriple_admissible_forall (fun v : Nat => iprop(p ↦ v))
      (fun _ _ => iprop(p ↦ 0))) ?_
  intro loop hLoop v
  step* 1
  by_cases h : value = 0
  · simp only [h, ↓reduceIte]
    step
    apply entails_pure_l
    intro hValue
    subst v
    apply postWand_intro
    intro _
    iframe
  · simp only [h, ↓reduceIte]
    step*

end Aeneas.SepLogic
