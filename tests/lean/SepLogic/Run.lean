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
open Aeneas.Std (Heap MutRawPtr RawPtr Result U32)
open Aeneas.Std.MutRawPtr (alloc free write)
open Aeneas.Std.RawPtr (read)

/-! ## A closed program -/

def roundTrip : Result U32 := do
  let p ← alloc 1#u32
  let value ← read p
  write p (value.wrapping_add 41#u32)
  let result ← read p
  free p
  pure result

theorem roundTrip.spec : ⦃ emp ⦄ roundTrip ⦃⇓ result => ⌜result = 42#u32⌝⦄ := by
  unfold roundTrip
  step*
  subst_vars
  rfl

def leaky : Result Unit := do
  let _ ← alloc 1#u32
  pure ()

theorem leaky.spec : ⦃ emp ⦄ leaky ⦃⇓ emp⦄ := by
  unfold leaky
  step*

/-! ## A program with an unchanged frame -/

private def source : MutRawPtr U32 := ⟨0, 0⟩
private def spare : MutRawPtr U32 := ⟨1, 0⟩

/-- The heap of the bytes `q` addresses, encoding `value`. -/
private def cell (q : MutRawPtr U32) (value : U32) : Heap := q.singleton value

/-- Ownership is byte-granular and runs of bytes compose by disjoint union, so
this computes. -/
private def initial : Heap :=
  cell source 1#u32 ∪ cell spare 7#u32

private theorem source_ne_spare : source.base ≠ spare.base := by decide

private theorem initial_disjoint :
    PartialCommMonoid.Compatible (cell source 1#u32) (cell spare 7#u32) :=
  RawPtr.disjoint_singleton source_ne_spare

private theorem cell_holds (q : MutRawPtr U32) (value : U32) (hOffset : q.offset = 0) :
    (q ↦ value) (cell q value) :=
  (RawPtr.pointsTo_holds q value _).mpr
    ⟨RawPtr.aligned_of_offset_eq_zero hOffset, Heap.Sub.refl _⟩

private theorem initial_pre : (source ↦ 1#u32) initial :=
  (source ↦ 1#u32).up_closed (cell_holds source 1#u32 rfl)
    (Heap.Sub.union_left initial_disjoint)

example : iwp true (Fixtures.incr_ptr source) (fun _ => source ↦ 2#u32) initial :=
  Fixtures.incr_ptr.spec source 1#u32 initial initial_pre

example :
    ⦃ source ↦ 1#u32 ∗ spare ↦ 7#u32 ⦄ Fixtures.incr_ptr source
      ⦃⇓ source ↦ 2#u32 ∗ spare ↦ 7#u32⦄ := by
  step*

example : iwp true (Fixtures.incr_ptr source)
    (fun _ => source ↦ 2#u32 ∗ spare ↦ 7#u32) initial :=
  ispec_frame (Fixtures.incr_ptr.spec source 1#u32) (spare ↦ 7#u32) initial
    ⟨cell source 1#u32, cell spare 7#u32, initial_disjoint, rfl,
      cell_holds source 1#u32 rfl, cell_holds spare 7#u32 rfl⟩

end SepLogic
