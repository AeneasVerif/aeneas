module

public import RawBoxProofs
public import Aeneas.Std.Heap.Notation
public import Aeneas.Std.Heap.Lifecycle
import all RawBoxProofs
import all Aeneas.Std.Heap.Initialization
import all Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_memory_views

/- Manual allocator boundary for the fixed Layout::new::<u32>() client.
   `available` records the external allocator's success/failure outcome; it is
   not a Rust argument. Successful placement is still demonic. `none` represents
   the null result, and OOM records the nonreturning handle_alloc_error branch.
   The WP accepts that abort without inventing a return value. -/
def allocate_word (available : Bool) : Result (Option (MutRawPtr U32)) :=
  if available then do
    let p ← Result.allocatingModify (State.allocUninitialized raw_box.u32Repr 1)
    pure (some p)
  else pure none

def first_heap_write (available : Bool) (value : U32) : Result U32 := do
  let allocation ← allocate_word available
  match allocation with
  | none => Result.oom
  | some word =>
    MutRawPtr.write raw_box.u32Repr word value
    let result ← RawPtr.read raw_box.u32Repr word
    Result.checkedModify (State.dealloc raw_box.u32Repr word 1)
    pure result

/-- The null-allocation branch does not return a fabricated value or touch memory. -/
theorem first_heap_write.allocation_failure (value : U32) :
    first_heap_write false value = Result.oom := by
  simp [first_heap_write, allocate_word, pure, bind_ok]

theorem first_heap_write.failure_accepted (value : U32) (s₀ : Heap)
    (post : U32 → Heap → Prop) :
    HeapWP.Spec (first_heap_write false value) post s₀ := by
  rw [first_heap_write.allocation_failure]
  exact HeapWP.Spec.oom

/-- **Spec theorem for `raw_memory_views::first_heap_write`**
    On allocator success, the first write initializes unreadable
    storage, the read returns exactly `value`, and physical deallocation consumes
    ownership. Every compatible placement and every external frame are covered. -/
theorem first_heap_write.spec (available : Bool) (value : U32) (s₀ : Heap) (F : Fragment)
    (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (first_heap_write available value)
      (fun result s₁ => result = value ∧ Fragment.Matches s₁ F ∧ s₁.Inv) s₀ := by
  cases available
  · exact first_heap_write.failure_accepted value s₀ _
  ·
    simp only [first_heap_write, allocate_word, ↓reduceIte, pure, Aeneas.Std.bind_assoc, bind_ok]
    apply HeapWP.Spec.bind (HeapWP.allocUninitialized.spec raw_box.u32Repr s₀ F hi hm)
    rintro p s₁ ⟨authority, h₁, hd₁, hm₁, hi₁, hp₁⟩
    have write : HeapWP.RootTriple [p.provenance]
        (block raw_box.u32Repr p p.address
          (List.replicate raw_box.u32Repr.size (.shared 0 .uninit)))
        (MutRawPtr.write raw_box.u32Repr p value)
        (fun _ => pointsTo raw_box.u32Repr p p.address value) := by
      have init := SepLogic.write.spec raw_box.u32Repr p p.address
        (Vector.replicate raw_box.u32Repr.size .uninit) value
        (raw_box.u32Repr_noPointers value) (by decide)
      have bytes :
          ((Vector.replicate raw_box.u32Repr.size Byte.uninit).map (Cell.shared 0)).toList =
            List.replicate raw_box.u32Repr.size (.shared 0 .uninit) := by
        simp only [Vector.toList_map, Vector.toList_replicate, List.map_replicate]
      rw [bytes] at init
      apply HeapWP.RootTriple.checkedModify init
      rintro s _ s' ⟨data, encoded, run⟩ root hr
      exact hr.modify run
    apply HeapWP.Spec.bind (HeapWP.RootTriple.frame
      (R := alloc raw_box.u32Repr p p.address 1 true) write
      h₁ F s₁ ((sep_comm _ _ _).mp hp₁) hd₁ hm₁ hi₁ (by simpa using authority))
    rintro _ s₂ ⟨authority₂, h₂, hd₂, hm₂, hi₂, hp₂⟩
    apply HeapWP.Spec.bind (HeapWP.RootTriple.read_owned (roots := [p.provenance])
      raw_box.u32Repr p p.address value true (by decide)
      h₂ F s₂ ((sep_comm _ _ _).mp hp₂) hd₂ hm₂ hi₂ authority₂)
    rintro result s₃ ⟨authority₃, h₃, hd₃, hm₃, hi₃, hr, hp₃⟩
    apply HeapWP.Spec.bind (HeapWP.dealloc.spec raw_box.u32Repr p p.address value
      s₃ (by decide) (authority₃ p.provenance (by simp)) h₃ F hp₃ hd₃ hm₃ hi₃)
    rintro _ s₄ ⟨h₄, _, hm₄, hi₄, rfl⟩
    exact (HeapWP.Spec.pure _ _ _).mpr ⟨hr, by simpa using hm₄, hi₄⟩

end raw_memory_views
