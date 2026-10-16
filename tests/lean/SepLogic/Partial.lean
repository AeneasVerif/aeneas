import SepLogic.Fixtures

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Data.Coinductive

open Aeneas.Std.WP

open Aeneas.Std (Heap MutRawPtr RawPtr Result loop)
open Aeneas.Std.MutRawPtr (write)
open Aeneas.Std.alloc.boxed.Box (into_raw from_raw)
open Aeneas.Std.RawPtr (read)

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ Fixtures.incr_ptr p ⦃ p ↦ value + 1⦄div := by
  step*

example (value : Nat) :
    ⦃ emp ⦄ Fixtures.incr_borrow value ⦃ result => ⌜result = value + 1⌝⦄div := by
  step*

example (x : Nat) :
    (do
      let y ← Fixtures.add1 x
      Fixtures.add1 y) ⦃ y => y = x + 2⦄div := by
  step*

def roundTripPartial : Result Nat := do
  let p ← into_raw (1 : Nat)
  let value ← read p
  write p (value + 41)
  let result ← read p
  let _ ← from_raw p
  pure result

theorem roundTripPartial.spec :
    ⦃ emp ⦄ roundTripPartial ⦃ result => ⌜result = 42⌝⦄div := by
  unfold roundTripPartial
  step*

example : ⦃ emp ⦄ Fixtures.incr_borrow 1 ⦃ result => ⌜result = 2⌝⦄div :=
  ispec_dispec (Fixtures.incr_borrow.spec 1)

example (p : MutRawPtr Nat) : ⦃ p ↦ 1 ⦄ (pure 5 : Result Nat) ⦃ v => ⌜v = 5⌝ ∗ p ↦ 1⦄div := by
  step*

example (p q : MutRawPtr Nat) (x : Nat) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9) ⦄ Fixtures.incr_ptr p ⦃ iprop(q ↦ 9 ∗ p ↦ (x + 1))⦄div := by
  step*

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ Fixtures.incr_ptr p ⦃ emp⦄div := by
  step*

/- The `i` tactics reach the entailment behind `dispec` through `iwp =>`, and `step` through the
same unfolding. -/
example (cell : Nat → IProp) (m : Result Unit) (h : ∀ x, ⦃ cell x ⦄ m ⦃ _ => emp ⦄div) :
    ⦃ iprop(∃ x, cell x) ⦄ m ⦃ _ => emp ⦄div := by
  iwp => iintro x
  exact h x

example (cell : Nat → IProp) (alloc use : Result Unit)
    (halloc : ⦃ emp ⦄ alloc ⦃ _ => ∃ v, ⌜0 < v⌝ ∗ cell v ⦄div)
    (huse : ∀ v, 0 < v → ⦃ cell v ⦄ use ⦃ _ => emp ⦄div) :
    ⦃ emp ⦄ (do alloc; use) ⦃ _ => emp ⦄div := by
  step with halloc as ⟨v, hv⟩
  guard_hyp hv : 0 < v
  step*

example (cell : Nat → IProp) (alloc : Result Nat) (use : Nat → Result Unit)
    (halloc : ⦃ emp ⦄ alloc ⦃ r => ∃ w, ⌜0 < r⌝ ∗ cell w ⦄div)
    (huse : ∀ v w, 0 < v → ⦃ cell w ⦄ use v ⦃ _ => cell w ⦄div) :
    ⦃ emp ⦄ (do let r ← alloc; use r) ⦃ _ => ∃ w, cell w ⦄div := by
  step*

section

unseal Result

example (p : MutRawPtr Nat) (Q : IPost Nat) : ¬ dispec emp (read p) Q := by
  intro hTriple
  rw [dispec_iff] at hTriple
  have hSpec := hTriple emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.RawPtr.read, Result.guardedModify] at hSpec
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isValid_empty p hContains

end

example (Q : IPost Nat) : dispec emp (Result.div : Result Nat) Q :=
  dispec_div

example (Q : IPost Nat) : ¬ ispec emp (Result.div : Result Nat) Q := by
  rw [ispec_iff]
  intro hTriple
  exact (hTriple emp Heap.empty ((entails_of_eq (sep_emp_r_eq emp).symm) Heap.empty trivial)).div_false

def incrForever (p : MutRawPtr Nat) : Result Empty := do
  let value ← read p
  write p (value + 1)
  incrForever p
partial_fixpoint

theorem incrForever.spec (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incrForever p ⦃ emp⦄div := by
  revert value
  refine incrForever.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃ emp⦄div)
    (dispec_admissible_forall (fun v : Nat => iprop(p ↦ v)) (fun _ _ => emp)) ?_
  intro loop hLoop v
  step*

def countdown (p : MutRawPtr Nat) : Result Unit := do
  let value ← read p
  if value = 0 then
    pure ()
  else do
    write p (value - 1)
    countdown p
partial_fixpoint

theorem countdown.spec (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ countdown p ⦃ p ↦ 0⦄div := by
  revert value
  refine countdown.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃ p ↦ 0⦄div)
    (dispec_admissible_forall (fun v : Nat => iprop(p ↦ v))
      (fun _ _ => iprop(p ↦ 0))) ?_
  intro loop hLoop v
  step*
  -- `p ↦ v ⊢ p ↦ 0` with `value = v` and `value = 0`: `iframe` does not chain the equalities
  subst_vars
  iframe

def waitZero (p : MutRawPtr Nat) (rounds : Nat) : Result Nat := do
  let value ← read p
  if value = 0 then pure rounds else waitZero p (rounds + 1)
partial_fixpoint

theorem waitZero.spec (p : MutRawPtr Nat) (value rounds : Nat) :
    ⦃ p ↦ value ⦄ waitZero p rounds ⦃ _ => p ↦ value⦄div := by
  revert rounds
  dspec_induction waitZero
  intro loop hLoop rounds
  step*

end SepLogic
