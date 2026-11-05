module

public import RawZmijMwe.Reuse
public import Aeneas.Std.Heap.Execution
import all RawZmijMwe.Decimal
import all RawZmijMwe.Formatter
import all RawRyuMwe.Storage
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Core.PtrOps
import all Aeneas.Std.Slice
import all Aeneas.Std.Primitives
import all Aeneas.Std.Scalar.Ops.Add

@[expose] public section

open Aeneas Aeneas.Std scalar_mwe HeapWP

namespace raw_zmij_mwe.execution

def address : BasePtr := 256#usize
def old : Vector Aeneas.Std.Byte 4 := Vector.replicate 4 .uninit
def updated : Vector Aeneas.Std.Byte 4 := #v[.data 48#u8, .uninit, .uninit, .uninit]
def start : RawPtr U8 := ⟨0, address⟩
def finish : RawPtr U8 := ⟨0, 257#usize⟩
def origin : RawPtr U8 := ⟨1, address⟩
def ptr : RawPtr U8 := ⟨2, address⟩

def create (bytes : List Aeneas.Std.Byte) (depth : Nat) (s : Heap) :=
  s.createRepr ⟨address, 0, bytes.map (Cell.shared depth), false, true, true⟩
def s₁ : Heap := ((create old.toList 0 Heap.empty).getD (0, Heap.empty)).2
def s₂ : Heap :=
  (Heap.write Repr.u8 start 48#u8 #v[.data 48#u8] rfl s₁).getD Heap.empty
def s₃ : Heap := (Heap.endExposureAt Repr.u8 start 4 0 s₂).getD Heap.empty
def s₄ : Heap := ((create updated.toList 1 s₃).getD (0, Heap.empty)).2
def s₅ : Heap := (Heap.endExposureAt Repr.u8 origin 4 1 s₄).getD Heap.empty
def s₆ : Heap := ((create updated.toList 1 s₅).getD (0, Heap.empty)).2
def s₇ : Heap := (Heap.shareRange Repr.u8 ptr 1 s₆).getD Heap.empty
def s₈ : Heap := (Heap.endShareRange Repr.u8 ptr 1 s₇).getD Heap.empty
def finalHeap : Heap := (Heap.endExposureAt Repr.u8 ptr 4 1 s₈).getD Heap.empty
def output : Slice U8 := Slice.from [48#u8] (by scalar_tac)

private theorem selected {α : Type} (run : Option α) (fallback : α)
    (success : run.isSome = true) : run = some (run.getD fallback) := by
  cases run
  · contradiction
  · rfl

private theorem created (run : Option (Nat × Heap)) (id : Nat)
    (success : run.map Prod.fst = some id) :
    run = some (id, (run.getD (0, Heap.empty)).2) := by
  cases run
  · contradiction
  · rename_i result
    have same := Option.some.inj success
    rw [← same]
    rfl

/-- This witness executes the formatter itself, including its decimal writer
    and all backward computations, rather than a parallel heap-only trace. -/
theorem format_zero_runs :
    Runs (DecimalBuffer.format_and_return old 0#u8 address)
      Heap.empty (output, updated) finalHeap := by
  simp only [DecimalBuffer.format_and_return, DecimalBuffer.format,
    DecimalBuffer.as_mut_ptr, DecimalBuffer.as_mut_ptr_back, DecimalBuffer.as_ptr,
    Std.bind_assoc, bind_ok, uncurry_apply_pair]
  apply Runs.bind (value := start) (s₁ := s₁)
  · apply Runs.allocatingModify
    exact ⟨some 0, created _ _ (by native_decide), rfl⟩
  have writer : write_decimal start 0#u8 =
      (do MutRawPtr.write Repr.u8 start 48#u8
          RawPtr.add Repr.u8 start 1#usize) := by
    have addition : 48#u8 + 0#u8 = Result.ok 48#u8 := by rfl
    simp [write_decimal, write_tail, write_last, emit, pure, bind_ok,
      uncurry_apply_pair, addition]
  rw [writer]
  apply Runs.bind (value := finish) (s₁ := s₂)
  · apply Runs.bind (value := ()) (s₁ := s₂)
    · apply Runs.checkedModify
      exact ⟨#v[.data 48#u8], rfl, selected _ Heap.empty (by native_decide)⟩
    · exact Runs.checkedModify ⟨by native_decide, rfl⟩
  apply Runs.bind (value := updated) (s₁ := s₂)
  · apply Runs.checkedModify
    refine ⟨(s₂.allocations 0).getD ⟨address, 0, [], false, true, true⟩,
      selected _ _ (by native_decide), ?_, ?_, ?_, rfl⟩
    · native_decide
    · native_decide
    · native_decide
  apply Runs.bind (value := ()) (s₁ := s₃)
  · exact Runs.checkedModify (selected _ Heap.empty (by native_decide))
  apply Runs.bind (value := origin) (s₁ := s₄)
  · apply Runs.allocatingModify
    exact ⟨some 0, created _ _ (by native_decide), rfl⟩
  apply Runs.bind (value := 1#isize) (s₁ := s₄)
  · exact Runs.checkedModify ⟨by native_decide, rfl⟩
  apply Runs.bind (value := ()) (s₁ := s₅)
  · exact Runs.checkedModify (selected _ Heap.empty (by native_decide))
  apply Runs.bind (value := ptr) (s₁ := s₆)
  · apply Runs.allocatingModify
    exact ⟨some 0, created _ _ (by native_decide), rfl⟩
  have cast : IScalar.hcast .Usize 1#isize = 1#usize := by native_decide
  rw [cast]
  simp only [core.slice.raw.from_raw_parts, Std.bind_assoc]
  apply Runs.bind (value := [48#u8]) (s₁ := s₇)
  · apply Runs.checkedModify
    change Heap.readRange Repr.u8 ptr 1 s₆ = some [48#u8] ∧
      Heap.shareRange Repr.u8 ptr 1 s₆ = some s₇
    exact ⟨by native_decide, selected _ Heap.empty (by native_decide)⟩
  simp only [List.length_cons, List.length_nil]
  have bound : 1 ≤ Usize.max := by scalar_tac
  simp only [bound, ↓reduceDIte, Std.bind_assoc, bind_ok, uncurry_apply_pair]
  apply Runs.bind (value := ()) (s₁ := s₈)
  · apply Runs.checkedModify
    change Heap.readRange Repr.u8 ptr 1 s₇ = some [48#u8] ∧
      Heap.endShareRange Repr.u8 ptr 1 s₇ = some s₈
    exact ⟨by native_decide, selected _ Heap.empty (by native_decide)⟩
  apply Runs.bind (value := ()) (s₁ := finalHeap)
  · exact Runs.checkedModify (selected _ Heap.empty (by native_decide))
  exact Runs.pure _ _

end raw_zmij_mwe.execution
