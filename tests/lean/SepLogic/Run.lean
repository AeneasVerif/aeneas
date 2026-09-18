import SepLogic.Fixtures

/-!
# Complete heap programs

Specifications for closed programs and programs with an unchanged frame.
Interpreter and execution-adequacy checks belong with the operational semantics
on `cezar/sm-semantics`.
-/

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Std.WP
open Aeneas.Std (Heap MutRawPtr RawPtr Result)
open Aeneas.Std.MutRawPtr (alloc free write)
open Aeneas.Std.RawPtr (read)

/-! ## A closed program -/

def roundTrip : Result Nat := do
  let p ← alloc (1 : Nat)
  let value ← read p
  write p (value + 41)
  let result ← read p
  free p
  pure result

theorem roundTrip.spec : ⦃ emp ⦄ roundTrip ⦃⇓ result => ⌜result = 42⌝⦄ := by
  unfold roundTrip
  step*

def leaky : Result Unit := do
  let _ ← alloc (1 : Nat)
  pure ()

theorem leaky.spec : ⦃ emp ⦄ leaky ⦃⇓ emp⦄ := by
  unfold leaky
  step*

/-! ## A program with an unchanged frame -/

private def source : MutRawPtr Nat := ⟨0, 0⟩
private def spare : MutRawPtr Nat := ⟨1, 0⟩

/-- The heap of the single slot `q` addresses, holding `value`. -/
private def cell (q : MutRawPtr Nat) (value : Nat) : Heap := q.singleton value

/-- Ownership is slot-granular and slots compose by disjoint union, so this
computes. -/
private def initial : Heap :=
  cell source 1 ∪ cell spare 7

private theorem source_ne_spare : source ≠ spare := by decide

private theorem initial_disjoint :
    PartialCommMonoid.Compatible (cell source 1) (cell spare 7) :=
  RawPtr.disjoint_singleton source_ne_spare

private theorem initial_pre : (source ↦ 1) initial :=
  Heap.Sub.union_left initial_disjoint

example : iwp true (Fixtures.incr_ptr source) (fun _ => source ↦ 2) initial :=
  Fixtures.incr_ptr.spec source 1 initial initial_pre

example :
    ⦃ source ↦ 1 ∗ spare ↦ 7 ⦄ Fixtures.incr_ptr source
      ⦃⇓ source ↦ 2 ∗ spare ↦ 7⦄ := by
  step*

example : iwp true (Fixtures.incr_ptr source)
    (fun _ => source ↦ 2 ∗ spare ↦ 7) initial :=
  ispec_frame (Fixtures.incr_ptr.spec source 1) (spare ↦ 7) initial
    ⟨cell source 1, cell spare 7, initial_disjoint, rfl,
      Heap.Sub.refl _, Heap.Sub.refl _⟩

end SepLogic
