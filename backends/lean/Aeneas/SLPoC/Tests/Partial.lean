import Aeneas.SLPoC.Tests.Examples.Basic

/-!
# Partial correctness

`Aeneas.SLPoC.ST` states the divergence-tolerant triple `dtriple`, written
`⦃P⦄ m ⦃⇓ x => Q⦄div`.  These are the tests that it proves what a total triple
proves of a program that stops, that the automation drives it — through the
lifting of the total specifications, which are the ones `@[step]` collects — and
that it proves what a total triple cannot: a loop that never leaves.
-/

namespace Aeneas.SLPoC

open Aeneas.Data.Coinductive

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
def roundTripPartial : St Nat := do
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
example (p : Ptr Nat) : ⦃ p ↦ 1 ⦄ (pure 5 : St Nat) ⦃⇓ v => ⌜v = 5⌝ ∗ p ↦ 1⦄div := by
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

/-- Being stuck, on the other hand, is not permitted: a read through a pointer
nothing owns has no partial triple either, since `PartialSpec` proves the guard
of every event it reaches exactly as `TotalSpec` does. -/
example (p : Ptr Nat) (Q : IPost Nat) : ¬ dtriple emp (read p) Q := fun hTriple =>
  not_contains_empty _
    (PartialSpec.vis_view (dtriple_apply hTriple trivial)).choose.contains

/-! ## What only partial correctness proves

`ITree.div` — the tree of an unproductive recursion — satisfies every partial
triple and no total one at all. -/

example (Q : IPost Nat) : dtriple emp (ITree.div : St Nat) Q :=
  dtriple_div

example (Q : IPost Nat) : ¬ triple emp (ITree.div : St Nat) Q := fun hTriple =>
  spec_div Q empty (triple_apply hTriple trivial)

/-! ## A loop that never leaves

`dtriple_iter` asks for an invariant the body restores and for nothing else: no
measure, no variant, no proof that the loop is ever left.  The loop below never
is, and it owns the cell it increments for as long as it runs. -/

/-- Increment the cell `p` for ever. -/
def incrForever (p : Ptr Nat) : St Empty :=
  ITree.iter
    (fun _ : Unit => do
      let value ← read p
      update p (value + 1)
      pure (.inl ()))
    ()

theorem incrForever.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incrForever p ⦃⇓ emp⦄div := by
  unfold incrForever
  refine dtriple_conseq (Q' := fun _ => emp)
    (dtriple_iter (J := fun _ => iprop(∃ v, p ↦ v)) (Q := fun _ => emp) ?_ ())
    (entails_exists_r value (entails_refl _)) (fun _ => entails_refl _)
  intro _
  apply dtriple_exists
  intro v
  step*

/-- The same loop, defined by a recursion of its own rather than by the loop
combinator: `partial_fixpoint` builds it as the limit of its approximations, and
`dtriple_admissible` is what lets the induction principle it comes with prove a
triple about that limit. -/
def incrForeverRec (p : Ptr Nat) : St Empty := do
  let value ← read p
  update p (value + 1)
  incrForeverRec p
partial_fixpoint

theorem incrForeverRec.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incrForeverRec p ⦃⇓ emp⦄div := by
  revert value
  refine incrForeverRec.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃⇓ emp⦄div)
    (dtriple_admissible_forall (fun v : Nat => iprop(p ↦ v)) (fun _ _ => emp)) ?_
  intro loop hLoop v
  step*

/-- The same rule proves a loop that does stop.  Partial correctness claims only
that *if* the countdown leaves, the cell it owns is zero — and proving that much
needs the invariant alone, where a total triple would also need the measure that
`value` decreases. -/
def countdown (p : Ptr Nat) : St Unit :=
  ITree.iter
    (fun _ : Unit => do
      let value ← read p
      if value = 0 then
        pure (.inr ())
      else do
        update p (value - 1)
        pure (.inl ()))
    ()

theorem countdown.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ countdown p ⦃⇓ p ↦ 0⦄div := by
  unfold countdown
  refine dtriple_conseq (Q' := fun _ => iprop(p ↦ 0))
    (dtriple_iter (J := fun _ => iprop(∃ v, p ↦ v))
      (Q := fun _ => iprop(p ↦ 0)) ?_ ())
    (entails_exists_r value (entails_refl _)) (fun _ => entails_refl _)
  intro _
  apply dtriple_exists
  intro v
  step*
  exact entails_pure_l fun hZero => hZero ▸ entails_refl _

end Aeneas.SLPoC
