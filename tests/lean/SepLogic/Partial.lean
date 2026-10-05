import SepLogic.Fixtures

/-!
# Partial correctness

`Aeneas.Std.WP` states the divergence-tolerant ispec `dispec`, written
`⦃P⦄ m ⦃⇓ x => Q⦄div`.  These are the tests that it proves what a total ispec
proves of a program that stops, that the automation drives it — through the
lifting of the total specifications, which are the ones `@[step]` collects — and
that it proves what a total ispec cannot: a loop that never leaves.
-/

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Data.Coinductive

open Aeneas.Std.WP

open Aeneas.Std (Heap MutRawPtr RawPtr Result U32 UScalar loop)
open Aeneas.Std.MutRawPtr (alloc free write)
open Aeneas.Std.RawPtr (read)

/-! ## The automation drives a partial goal

`step` and `step*` work on `dispec` exactly as on `ispec`: the `@[step]`
specifications state *total* correctness, and `ispec_dispec` lifts each of
them where it is applied, as `Aeneas.Std.WP.spec_dspec` does for `Result`. -/

example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ Fixtures.incr_ptr p ⦃⇓ p ↦ value.wrapping_add 1#u32⦄div := by
  step*

example (value : U32) :
    ⦃ emp ⦄ Fixtures.incr_borrow value ⦃⇓ result => ⌜result = value.wrapping_add 1#u32⌝⦄div := by
  step*

example (x : Nat) :
    (do
      let y ← Fixtures.add1 x
      Fixtures.add1 y) ⦃⇓ y => y = x + 2⦄div := by
  step*

/-- A program written out in full, allocation to deallocation, proved partially
correct with no more work than it takes to prove it totally correct. -/
def roundTripPartial : Result U32 := do
  let p ← alloc 1#u32
  let value ← read p
  write p (value.wrapping_add 41#u32)
  let result ← read p
  free p
  pure result

theorem roundTripPartial.spec :
    ⦃ emp ⦄ roundTripPartial ⦃⇓ result => ⌜result = 42#u32⌝⦄div := by
  unfold roundTripPartial
  step*
  subst_vars
  rfl

/-- And a total proof is a partial one, so it need not be redone. -/
example : ⦃ emp ⦄ Fixtures.incr_borrow 1#u32 ⦃⇓ result => ⌜result = 2#u32⌝⦄div :=
  ispec_dispec (Fixtures.incr_borrow.spec 1#u32)

/-- The proof-mode tactics have partial counterparts: `dwp_pures` for a terminal
`pure`, `dwp_apply` for a terminal call through the ramified frame rule, and
`dwp_mono` to weaken an `ispec` already proved. -/
example (p : MutRawPtr U32) :
    ⦃ p ↦ 1#u32 ⦄ (pure 5 : Result Nat) ⦃⇓ v => ⌜v = 5⌝ ∗ p ↦ 1#u32⦄div := by
  dwp_pures
  isimpl

example (p q : MutRawPtr U32) (x : U32) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9#u32) ⦄ Fixtures.incr_ptr p
      ⦃⇓ iprop(q ↦ 9#u32 ∗ p ↦ (x.wrapping_add 1#u32))⦄div := by
  dwp_apply (ispec_dispec (Fixtures.incr_ptr.spec p x))

example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ Fixtures.incr_ptr p ⦃⇓ emp⦄div := by
  dwp_mono (ispec_dispec (Fixtures.incr_ptr.spec p value))

/-! ## What partial correctness still owes

Divergence is permitted; being stuck is not. Execution-adequacy tests belong
with the operational semantics on `cezar/sm-semantics`. -/

section

unseal Result

/-- Being stuck, on the other hand, is not permitted: a read through a pointer
nothing owns has no partial specification either, since partial correctness
proves the guard of every event it reaches just as total correctness does. -/
example (p : MutRawPtr U32) (Q : IPost U32) : ¬ dispec emp (read p) Q := by
  intro hTriple
  rw [dispec_iff] at hTriple
  have hSpec := hTriple emp ∅ ((sep_emp_r emp).mpr ∅ trivial)
  simp only [Aeneas.Std.RawPtr.read, Result.guardedModify] at hSpec
  obtain ⟨hReadable, -⟩ := hSpec.vis_view
  exact RawPtr.not_contains_empty p (UScalar.byteRepr_size_pos _) hReadable.contains

end

/-! ## What only partial correctness proves

`Result.div` — the tree of an unproductive recursion — satisfies every partial
ispec and no total one at all. -/

example (Q : IPost Nat) : dispec emp (Result.div : Result Nat) Q :=
  dispec_div

example (Q : IPost Nat) : ¬ ispec emp (Result.div : Result Nat) Q := by
  rw [ispec_iff]
  intro hTriple
  exact (hTriple emp Heap.empty ((sep_emp_r emp).mpr Heap.empty trivial)).div_false

/-! ## A loop that never leaves

`partial_fixpoint` asks for an admissible invariant the recursive body restores
and for nothing else: no measure, no variant, no proof that the loop is ever
left. The loop below never is, and it owns the cell it increments for as long
as it runs. -/

/-- Increment the cell `p` for ever. -/
def incrForever (p : MutRawPtr U32) : Result Empty := do
  let value ← read p
  write p (value.wrapping_add 1#u32)
  incrForever p
partial_fixpoint

theorem incrForever.spec (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ incrForever p ⦃⇓ emp⦄div := by
  revert value
  refine incrForever.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃⇓ emp⦄div)
    (dispec_admissible_forall (fun v : U32 => iprop(p ↦ v)) (fun _ _ => emp)) ?_
  intro loop hLoop v
  step*

/-- The same rule proves a loop that does stop.  Partial correctness claims only
that *if* the countdown leaves, the cell it owns is zero — and proving that much
needs the invariant alone, where a total ispec would also need the measure that
`value` decreases. -/
def countdown (p : MutRawPtr U32) : Result Unit := do
  let value ← read p
  if value = 0#u32 then
    pure ()
  else do
    write p (value.wrapping_sub 1#u32)
    countdown p
partial_fixpoint

theorem countdown.spec (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ countdown p ⦃⇓ p ↦ 0#u32⦄div := by
  revert value
  refine countdown.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃⇓ p ↦ 0#u32⦄div)
    (dispec_admissible_forall (fun v : U32 => iprop(p ↦ v))
      (fun _ _ => iprop(p ↦ 0#u32))) ?_
  intro loop hLoop v
  step*

/-! ## `dspec_induction` on a separation-logic goal

The boilerplate above — the motive, the admissibility argument — is what
`dspec_induction` writes on its own.  It closes the admissibility side-goal with
the theorems carrying the `dspec_admissible` attribute, and `dispec_func_admissible`
is the one registered for `dispec`, so the tactic drives a separation-logic goal
exactly as it drives a pure `Std.WP.dspec` one. -/

/-- Poll `p` until it holds `0`, counting the rounds it took. -/
def waitZero (p : MutRawPtr U32) (rounds : Nat) : Result Nat := do
  let value ← read p
  if value = 0#u32 then pure rounds else waitZero p (rounds + 1)
partial_fixpoint

/-- Polling leaves `p` alone: the invariant is all the proof needs, and the
tactic asks for nothing else. -/
theorem waitZero.spec (p : MutRawPtr U32) (value : U32) (rounds : Nat) :
    ⦃ p ↦ value ⦄ waitZero p rounds ⦃⇓ _ => p ↦ value⦄div := by
  revert rounds
  dspec_induction waitZero
  intro loop hLoop rounds
  step*

end SepLogic
