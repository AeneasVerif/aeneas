module

public import RawMemoryViews.Provenance
public import RawMemoryViews.Initialization
public import RawRyuMwe.Storage
import all Aeneas.Std.Heap.Initialization
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Core.Ptr
import all RawBoxProofs

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_memory_views

set_option maxHeartbeats 1000000

def pointerBytes (p : RawPtr U32) : List Aeneas.Std.Byte :=
  (Repr.pointerEncoding p).toList

def copy_saved_pointer (word : RawPtr U32) (sourceAddress destinationAddress : BasePtr) :
    Result (RawPtr U32) := do
  let source ← exposeBytes (pointerBytes word) 1 sourceAddress
  let destination ← exposeBytes (List.replicate pointerWidth .uninit) 0 destinationAddress
  let copied ← copy_stored_pointer (source.cast _) (destination.cast _)
  closeBytes destination pointerWidth 0
  closeBytes source pointerWidth 1
  .ok copied

/-- Complete stack-slot scope: the saved pointer may already be dangling.
    No permission to its pointee is assumed or manufactured. -/
theorem copy_saved_pointer.spec (word : RawPtr U32)
    (sourceAddress destinationAddress : BasePtr)
    (sourceAligned : 8 ∣ sourceAddress.val) (destinationAligned : 8 ∣ destinationAddress.val)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (copy_saved_pointer word sourceAddress destinationAddress)
      (fun result s₁ => result = word ∧ s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  unfold copy_saved_pointer
  apply HeapWP.Spec.bind (exposeBytes.spec _ 1 sourceAddress s₀ F hi hm)
  rintro source s₁ ⟨sourceAddr, _, src, srcF, matching₁, inv₁, sourceOwns⟩
  apply HeapWP.Spec.bind
    (exposeBytes.spec _ 0 destinationAddress s₁ (src ∪ F) inv₁ matching₁)
  rintro destination s₂ ⟨destinationAddr, _, dst, dstFrame, matching₂, inv₂, destinationOwns⟩
  obtain ⟨dstSrc, dstF⟩ := Fragment.disjoint_union_right.mp dstFrame
  have pre :
      (storageAt destination (List.replicate pointerWidth .uninit) 0 ∗
        storageAt source (pointerBytes word) 1) (dst ∪ src) :=
    ⟨dst, src, dstSrc, rfl, destinationOwns, sourceOwns⟩
  have copy : HeapWP.Triple
      (bytesAt destination destination.address (List.replicate pointerWidth .uninit) ∗
        bytesAt source source.address (pointerBytes word) 1)
      (copy_stored_pointer (source.cast _) (destination.cast _))
      (fun result h => result = word ∧
        (bytesAt destination destination.address (pointerBytes word) ∗
          bytesAt source source.address (pointerBytes word) 1) h) := by
    have ht := copy_stored_pointer.spec (source.cast _) (destination.cast _)
      source.address destination.address word (Vector.replicate pointerWidth .uninit) 1
    simpa [HeapWP.Triple, sep, pointsTo, Repr.pointer, block, bytesAt, pointerBytes, RawPtr.cast,
      RawPtr.offsetFrom, Repr.u8, Vector.toList_map, sourceAddr, destinationAddr,
      sourceAligned, destinationAligned] using ht
  have body := preserve_two_storage destination source
    (List.replicate pointerWidth .uninit) (pointerBytes word)
    (pointerBytes word) (pointerBytes word) 0 1
    (copy_stored_pointer (source.cast _) (destination.cast _)) (fun result => result = word)
    (by simp [pointerBytes]) rfl copy
  apply HeapWP.Spec.bind (body (dst ∪ src) F s₂ pre
    (Fragment.disjoint_union_left.mpr ⟨dstF, srcF⟩)
    (by simpa only [Fragment.union_assoc] using matching₂) inv₂)
  rintro copied s₃ ⟨h₃, hd₃, hm₃, hi₃, copiedEq, a, b, hab, rfl, ha, hb⟩
  subst copied
  obtain ⟨aF, bF⟩ := Fragment.disjoint_union_left.mp hd₃
  have closing := closeBytes.state_spec destination (pointerBytes word) 0
    a (b ∪ F) s₃ ha (Fragment.disjoint_union_right.mpr ⟨hab, aF⟩)
    (by simpa only [Fragment.union_assoc] using hm₃) hi₃
  simp only [pointerBytes, Vector.length_toList] at closing
  apply HeapWP.Spec.bind closing
  rintro _ s₄ ⟨hi₄, hm₄, _, _⟩
  have closing := closeBytes.state_spec source (pointerBytes word) 1 b F s₄ hb bF hm₄ hi₄
  simp only [pointerBytes, Vector.length_toList] at closing
  apply HeapWP.Spec.bind closing
  rintro _ s₅ ⟨hi₅, hm₅, _, _⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, hi₅, hm₅⟩

/- The allocator outcome and stack placements are ghost parameters of this
   handwritten model. The ordering follows Rust: free the pointee, then expose
   the saved pointer and the initially uninitialized destination slot. -/
def copy_after_deallocation (available : Bool) (value : U32)
    (sourceAddress destinationAddress : BasePtr) : Result (Usize × Usize) := do
  let allocation ← allocate_word available
  match allocation with
  | none => Result.oom
  | some word =>
    MutRawPtr.write raw_box.u32Repr word value
    let before := word.address
    Result.checkedModify (State.dealloc raw_box.u32Repr word 1)
    let copied ← copy_saved_pointer word sourceAddress destinationAddress
    .ok (before, copied.address)

theorem copy_after_deallocation.spec (available : Bool) (value : U32)
    (sourceAddress destinationAddress : BasePtr)
    (sourceAligned : 8 ∣ sourceAddress.val) (destinationAligned : 8 ∣ destinationAddress.val)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (copy_after_deallocation available value sourceAddress destinationAddress)
      (fun result s₁ => result.1 = result.2 ∧ s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  cases available
  · simpa [copy_after_deallocation, allocate_word, bind_ok, pure] using
      (HeapWP.Spec.oom (Q := fun (result : Usize × Usize) s₁ =>
        result.1 = result.2 ∧ s₁.Inv ∧ Fragment.Matches s₁ F) (s := s₀))
  ·
    simp only [copy_after_deallocation, allocate_word, ↓reduceIte, pure,
      Aeneas.Std.bind_assoc, bind_ok]
    apply HeapWP.Spec.bind (HeapWP.allocUninitialized.spec raw_box.u32Repr s₀ F hi hm)
    rintro word s₁ ⟨authority, h₁, hd₁, hm₁, hi₁, hp₁⟩
    have write : HeapWP.RootTriple [word.provenance]
        (block raw_box.u32Repr word word.address
          (List.replicate raw_box.u32Repr.size (.shared 0 .uninit)))
        (MutRawPtr.write raw_box.u32Repr word value)
        (fun _ => pointsTo raw_box.u32Repr word word.address value) := by
      have init := SepLogic.write.spec raw_box.u32Repr word word.address
        (Vector.replicate raw_box.u32Repr.size .uninit) value
        (raw_box.u32Repr_noPointers value) (by decide)
      simp only [Vector.toList_map, Vector.toList_replicate, List.map_replicate] at init
      apply HeapWP.RootTriple.checkedModify init
      rintro s _ s' ⟨data, encoded, run⟩ root hr
      exact hr.modify run
    apply HeapWP.Spec.bind (HeapWP.RootTriple.frame
      (R := alloc raw_box.u32Repr word word.address 1 true) write
      h₁ F s₁ ((sep_comm _ _ _).mp hp₁) hd₁ hm₁ hi₁ (by simpa using authority))
    rintro _ s₂ ⟨authority₂, h₂, hd₂, hm₂, hi₂, hp₂⟩
    apply HeapWP.Spec.bind (HeapWP.dealloc.spec raw_box.u32Repr word word.address value
      s₂ (by decide) (authority₂ word.provenance (by simp))
      h₂ F ((sep_comm _ _ _).mp hp₂) hd₂ hm₂ hi₂)
    rintro _ s₃ ⟨h₃, _, hm₃, hi₃, rfl⟩
    apply HeapWP.Spec.bind (copy_saved_pointer.spec word sourceAddress destinationAddress
      sourceAligned destinationAligned s₃ F hi₃ (by simpa using hm₃))
    rintro copied s₄ ⟨rfl, hi₄, hm₄⟩
    exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, hi₄, hm₄⟩

end raw_memory_views
