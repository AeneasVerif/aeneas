module

public import RawMemoryViews.ProvenanceScoped
meta import RawMemoryViews.ProvenanceScoped
public import Aeneas.Std.Heap.Execution
import all RawMemoryViews.Initialization
import all RawMemoryViews.Provenance
import all RawRyuMwe.Storage
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Copy
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas Aeneas.Std scalar_mwe HeapWP

namespace raw_memory_views.execution

def word : RawPtr U32 := ⟨0, 256#usize⟩
def source : RawPtr U8 := ⟨1, 512#usize⟩
def destination : RawPtr U8 := ⟨2, 768#usize⟩
def s₁ := ((Heap.alloc raw_box.u32Repr 1 word.address Heap.empty).getD (word, Heap.empty)).2
def data := (raw_box.u32Bytes 0#u32).map Byte.data
def s₂ := (Heap.write raw_box.u32Repr word 0#u32 data rfl s₁).getD Heap.empty
def s₃ := (Heap.dealloc raw_box.u32Repr word 1 s₂).getD Heap.empty
def s₄ := ((s₃.createRepr ⟨source.address, 1, (pointerBytes word).map (Cell.shared 1),
  false, true, true⟩).getD (0, Heap.empty)).2
def s₅ := ((s₄.createRepr ⟨destination.address, 2,
  List.replicate pointerWidth (.shared 0 .uninit), false, true, true⟩).getD (0, Heap.empty)).2
def s₆ := (Heap.copyBytes (source.cast (RawPtr U32)) (destination.cast (RawPtr U32))
  pointerWidth s₅).getD Heap.empty
def s₇ := (Heap.endExposureAt Repr.u8 destination pointerWidth 0 s₆).getD Heap.empty
def finalHeap := (Heap.endExposureAt Repr.u8 source pointerWidth 1 s₇).getD Heap.empty

private theorem selected {α : Type} (run : Option α) (fallback : α)
    (success : run.isSome = true) : run = some (run.getD fallback) := by
  cases run
  · contradiction
  · rfl

private theorem paired {α : Type} (run : Option (α × Heap)) (value fallback : α)
    (success : run.map Prod.fst = some value) :
    run = some (value, (run.getD (fallback, Heap.empty)).2) := by
  cases run
  · contradiction
  · rename_i result
    rw [← Option.some.inj success]
    rfl

/-- Successful execution of the complete model, including real deallocation
    before the saved pointer is exposed and copied. -/
theorem copy_after_deallocation_runs :
    Runs (copy_after_deallocation true 0#u32 source.address destination.address)
      Heap.empty (word.address, word.address) finalHeap := by
  simp only [copy_after_deallocation, allocate_word, ↓reduceIte,
    Std.bind_assoc, pure, bind_ok]
  apply Runs.bind (value := word) (s₁ := s₁)
  · apply Runs.allocatingModify
    exact ⟨word.address, paired _ _ word (by native_decide)⟩
  apply Runs.bind (value := ()) (s₁ := s₂)
  · apply Runs.checkedModify
    exact ⟨data, rfl, selected _ Heap.empty (by native_decide)⟩
  apply Runs.bind (value := ()) (s₁ := s₃)
  · exact Runs.checkedModify (selected _ Heap.empty (by native_decide))
  simp only [copy_saved_pointer, copy_stored_pointer, Std.bind_assoc, bind_ok]
  apply Runs.bind (value := source) (s₁ := s₄)
  · apply Runs.allocatingModify
    exact ⟨some 1, paired _ _ 0 (by native_decide), rfl⟩
  apply Runs.bind (value := destination) (s₁ := s₅)
  · apply Runs.allocatingModify
    exact ⟨some 2, paired _ _ 0 (by native_decide), rfl⟩
  apply Runs.bind (value := ()) (s₁ := s₆)
  · exact Runs.checkedModify (selected _ Heap.empty (by native_decide))
  apply Runs.bind (value := word) (s₁ := s₆)
  · exact Runs.checkedModify ⟨by native_decide, rfl⟩
  apply Runs.bind (value := ()) (s₁ := s₇)
  · exact Runs.checkedModify (selected _ Heap.empty (by native_decide))
  apply Runs.bind (value := ()) (s₁ := finalHeap)
  · exact Runs.checkedModify (selected _ Heap.empty (by native_decide))
  exact Runs.pure _ _

theorem final_root_dead :
    (finalHeap.allocations word.provenance).map Block.alive = some false ∧
      Heap.read raw_box.u32Repr word finalHeap = none := by native_decide

end raw_memory_views.execution
