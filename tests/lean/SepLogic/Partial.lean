import SepLogic.Fixtures

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Data.Coinductive

open Aeneas.Std.WP

open Aeneas.Std (Heap MutRawPtr RawPtr Result loop U32)
open Aeneas.Std.MutRawPtr (write)
open Aeneas.Std.alloc.boxed.Box (into_raw from_raw)
open Aeneas.Std.RawPtr (read)

example (p : MutRawPtr U32) (value : U32) (h : value.val + 1 ≤ U32.max) :
    ⦃ p ↦ value ⦄ Fixtures.incr_ptr p ⦃ ∃ v, ⌜v.val = value.val + 1⌝ ∗ p ↦ v⦄div := by
  step*

example (value : U32) (h : value.val + 1 ≤ U32.max) :
    ⦃ emp ⦄ Fixtures.incr_borrow value ⦃ result => ⌜result.val = value.val + 1⌝⦄div := by
  step*

example (x : Nat) :
    (do
      let y ← Fixtures.add1 x
      Fixtures.add1 y) ⦃ y => y = x + 2⦄div := by
  step*

def roundTripPartial : Result U32 := do
  let p ← into_raw ⟨1#u32⟩
  let value ← read p
  let value' ← value + 41#u32
  write p value'
  let result ← read p
  let _ ← from_raw p
  pure result

theorem roundTripPartial.spec :
    ⦃ emp ⦄ roundTripPartial ⦃ result => ⌜result.val = 42⌝⦄div := by
  unfold roundTripPartial
  step*

example : ⦃ emp ⦄ Fixtures.incr_borrow 1#u32 ⦃ result => ⌜result.val = 1 + 1⌝⦄div :=
  ispec_dispec (Fixtures.incr_borrow.spec 1#u32 (by scalar_tac))

example (p : MutRawPtr U32) :
    ⦃ p ↦ 1#u32 ⦄ (pure 5 : Result Nat) ⦃ v => ⌜v = 5⌝ ∗ p ↦ 1#u32⦄div := by
  step*

example (p q : MutRawPtr U32) (x : U32) (h : x.val + 1 ≤ U32.max) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9#u32) ⦄ Fixtures.incr_ptr p
      ⦃ iprop(q ↦ 9#u32 ∗ ∃ v, ⌜v.val = x.val + 1⌝ ∗ p ↦ v)⦄div := by
  step*

example (p : MutRawPtr U32) (value : U32) (h : value.val + 1 ≤ U32.max) :
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

example (p : MutRawPtr U32) (Q : IPost U32) : ¬ dispec emp (read p) Q := by
  intro hTriple
  rw [dispec_iff] at hTriple
  have hSpec := hTriple emp Heap.empty (realizes_sep_emp.mpr realizes_emp_empty)
  simp only [Aeneas.Std.RawPtr.read, Result.checkedModify] at hSpec
  -- On the empty heap the read is not enabled: the checked request answers `none`, and the
  -- operation fails with `undef`
  have hNone := hSpec.vis_view.2 none Heap.empty
    ⟨fun ⟨_, _, hRead, _⟩ => by simp [Heap.read, Heap.empty] at hRead, rfl⟩
  simp [Result.ofOption] at hNone
  exact absurd hNone.vis_view (by simp)

end

example (Q : IPost Nat) : dispec emp (Result.div : Result Nat) Q :=
  dispec_div

example (Q : IPost Nat) : ¬ ispec emp (Result.div : Result Nat) Q := by
  rw [ispec_iff]
  intro hTriple
  exact (hTriple emp Heap.empty (realizes_sep_emp.mpr realizes_emp_empty)).div_false

def incrForever (p : MutRawPtr U32) : Result Empty := do
  let value ← read p
  write p (value.wrapping_add 1#u32)
  incrForever p
partial_fixpoint

theorem incrForever.spec (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ incrForever p ⦃ emp⦄div := by
  revert value
  refine incrForever.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃ emp⦄div)
    (dispec_admissible_forall (fun v : U32 => iprop(p ↦ v)) (fun _ _ => emp)) ?_
  intro loop hLoop v
  step*

def countdown (p : MutRawPtr U32) : Result Unit := do
  let value ← read p
  if value = 0#u32 then
    pure ()
  else do
    let value' ← value - 1#u32
    write p value'
    countdown p
partial_fixpoint

theorem countdown.spec (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ countdown p ⦃ p ↦ 0#u32⦄div := by
  revert value
  refine countdown.fixpoint_induct p
    (fun loop => ∀ v, ⦃ p ↦ v ⦄ loop ⦃ p ↦ 0#u32⦄div)
    (dispec_admissible_forall (fun v : U32 => iprop(p ↦ v))
      (fun _ _ => iprop(p ↦ 0#u32))) ?_
  intro loop hLoop v
  step*
  -- `p ↦ v ⊢ p ↦ 0` with `value = v` and `value = 0`: `iframe` does not chain the equalities
  subst_vars
  iframe

def waitZero (p : MutRawPtr U32) (rounds : Nat) : Result Nat := do
  let value ← read p
  if value = 0#u32 then pure rounds else waitZero p (rounds + 1)
partial_fixpoint

theorem waitZero.spec (p : MutRawPtr U32) (value : U32) (rounds : Nat) :
    ⦃ p ↦ value ⦄ waitZero p rounds ⦃ _ => p ↦ value⦄div := by
  revert rounds
  dspec_induction waitZero
  intro loop hLoop rounds
  step*

end SepLogic
