module

public import RawMemoryViews.Pointer
public import Aeneas.Std.Heap.Copy
public import Aeneas.Std.Heap.Lifecycle
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Copy
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_memory_views

/- The casts to byte pointers preserve both fields; the copy is the actual
   untyped Heap.copyBytes operation, not a substituted typed assignment. -/
def copy_stored_pointer (source destination : RawPtr (RawPtr U32)) : Result (RawPtr U32) := do
  HeapWP.copy_pointer source destination
  RawPtr.read (Aeneas.Std.Repr.pointer U32) destination

/-- **Spec theorem for `raw_memory_views::copy_stored_pointer`**
    Copying into writable (possibly uninitialized) storage preserves the exact
    pointer, including its provenance. It requires no pointee permission. -/
theorem copy_stored_pointer.spec (source destination : RawPtr (RawPtr U32))
    (sourceBase destinationBase : BasePtr) (target : RawPtr U32)
    (old : Vector Aeneas.Std.Byte (Aeneas.Std.Repr.pointer U32).size) (depth : Nat) :
    ⦃ block (Aeneas.Std.Repr.pointer U32) destination destinationBase (old.map (Cell.shared 0)).toList ∗
      pointsTo (Aeneas.Std.Repr.pointer U32) source sourceBase target depth ⦄
    copy_stored_pointer source destination
    ⦃ (result : RawPtr U32) => fun h => result = target ∧
      (pointsTo (Aeneas.Std.Repr.pointer U32) destination destinationBase target ∗
        pointsTo (Aeneas.Std.Repr.pointer U32) source sourceBase target depth) h ⦄ := by
  intro h F s₀ hp hd hm hi
  unfold copy_stored_pointer
  apply HeapWP.Spec.bind (HeapWP.copy_pointer_writable.spec source destination sourceBase
    destinationBase target old depth h F s₀ hp hd hm hi)
  rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  apply HeapWP.Spec.mono (HeapWP.frame
    (HeapWP.read.spec (Aeneas.Std.Repr.pointer U32) destination destinationBase target 0 (by decide))
    h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
  rintro result s₂ ⟨h₂, hd₂, hm₂, hi₂, post⟩
  exact ⟨h₂, hd₂, hm₂, hi₂, (sep_and_left _ _ _ _).mp post⟩

def same_address (p q : RawPtr U32) : Result Bool :=
  .ok (p.address == q.address)

def copy_and_use (source destination : RawPtr (RawPtr U32)) (value : U32) : Result U32 := do
  let target ← copy_stored_pointer source destination
  MutRawPtr.write raw_box.u32Repr target value
  RawPtr.read raw_box.u32Repr target

/-- A copied pointer supports subsequent access when the caller separately
    owns its pointee. Copying itself does not manufacture this permission. -/
theorem copy_and_use.spec (source destination : RawPtr (RawPtr U32))
    (sourceBase destinationBase targetBase : BasePtr) (target : RawPtr U32)
    (old : Vector Aeneas.Std.Byte (Aeneas.Std.Repr.pointer U32).size)
    (initial value : U32) :
    ⦃ (block (Aeneas.Std.Repr.pointer U32) destination destinationBase (old.map (Cell.shared 0)).toList ∗
      pointsTo (Aeneas.Std.Repr.pointer U32) source sourceBase target) ∗
      pointsTo raw_box.u32Repr target targetBase initial ⦄
    copy_and_use source destination value
    ⦃ (result : U32) => fun h => result = value ∧
      ((pointsTo (Aeneas.Std.Repr.pointer U32) destination destinationBase target ∗
        pointsTo (Aeneas.Std.Repr.pointer U32) source sourceBase target) ∗
        pointsTo raw_box.u32Repr target targetBase value) h ⦄ := by
  intro h F s₀ hp hd hm hi
  unfold copy_and_use
  apply HeapWP.Spec.bind (HeapWP.frame (R := pointsTo raw_box.u32Repr target targetBase initial)
    (copy_stored_pointer.spec source destination sourceBase destinationBase target old 0)
    h F s₀ hp hd hm hi)
  rintro copied s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  obtain ⟨copiedEq, slots⟩ :
      copied = target ∧
        ((pointsTo (Aeneas.Std.Repr.pointer U32) destination destinationBase target ∗
          pointsTo (Aeneas.Std.Repr.pointer U32) source sourceBase target) ∗
          pointsTo raw_box.u32Repr target targetBase initial) h₁ := by
    simpa only [sep_and_left] using hp₁
  subst copied
  have access := HeapWP.Triple.bind
    (HeapWP.write.spec raw_box.u32Repr target targetBase initial value
      (raw_box.u32Repr_noPointers value) (by decide))
    (fun _ => HeapWP.read.spec raw_box.u32Repr target targetBase value 0 (by decide))
  apply HeapWP.Spec.mono (HeapWP.frame
    (R := pointsTo (Aeneas.Std.Repr.pointer U32) destination destinationBase target ∗
      pointsTo (Aeneas.Std.Repr.pointer U32) source sourceBase target)
    access h₁ F s₁ ((sep_comm _ _ _).mp slots) hd₁ hm₁ hi₁)
  rintro result s₂ ⟨h₂, hd₂, hm₂, hi₂, post⟩
  obtain ⟨resultEq, post⟩ := (sep_and_left _ _ _ _).mp post
  exact ⟨h₂, hd₂, hm₂, hi₂, resultEq, (sep_comm _ _ _).mp post⟩

/-- Address comparison is pure and confers no memory permission. -/
theorem same_address.spec (p q : RawPtr U32) :
    ⦃ empty ⦄ same_address p q
    ⦃ (result : Bool) => fun h => result = (p.address == q.address) ∧ empty h ⦄ :=
  HeapWP.Triple.pure empty _

/-- A pointer with the same address but an unissued provenance cannot be read. -/
theorem same_address.unissued_read_rejected (p : RawPtr U32) (s : Heap)
    (hi : s.Inv) (id : Nat) (unissued : s.next ≤ id) :
    same_address p ⟨id, p.address⟩ = .ok true ∧
      Heap.read raw_box.u32Repr ⟨id, p.address⟩ s = none := by
  constructor
  · simp [same_address]
  · simp [Heap.read, hi.1 id unissued]

/-- Retiring a raw view preserves its pointer payload metadata, but removes
    access through that view even while the allocation itself may stay alive. -/
theorem retired_pointer_read_rejected (p : RawPtr U32) (s : Heap) :
    Heap.read raw_box.u32Repr p (s.retire p.provenance) = none := by
  cases hl : s.allocations p.provenance
  · simp [Heap.read, Heap.retire, update, hl]
  · simp [Heap.read, Heap.retire, update, hl, Heap.live]

/- Raw tail of copy_after_deallocation: safe stack slots are exposed explicitly.
   The allocator/null branch is shared with the first-write example. -/
def copy_after_deallocation_tail (word : RawPtr U32)
    (source destination : RawPtr (RawPtr U32)) : Result (Usize × Usize) := do
  let before := word.address
  Result.checkedModify (State.dealloc raw_box.u32Repr word 1)
  let copied ← copy_stored_pointer source destination
  pure (before, copied.address)

/-- **Raw-tail spec for `raw_memory_views::copy_after_deallocation`**
    Physical deallocation preserves the saved pointer's symbolic lanes.
    A subsequent byte copy and pointer load succeed and preserve its address;
    neither performs a dereference of the dead pointee. -/
theorem copy_after_deallocation_tail.spec (word : RawPtr U32) (value : U32)
    (source destination : RawPtr (RawPtr U32)) (sourceBase destinationBase : BasePtr)
    (old : Vector Aeneas.Std.Byte (Aeneas.Std.Repr.pointer U32).size)
    (s₀ : Heap) (authority : RootReturn s₀ word.provenance) :
    HeapWP.TripleAt
      ((alloc raw_box.u32Repr word word.address 1 true ∗
        pointsTo raw_box.u32Repr word word.address value) ∗
        (block (Aeneas.Std.Repr.pointer U32) destination destinationBase (old.map (Cell.shared 0)).toList ∗
          pointsTo (Aeneas.Std.Repr.pointer U32) source sourceBase word))
      (copy_after_deallocation_tail word source destination)
      (fun (before, after) h => before = word.address ∧ after = word.address ∧
        (pointsTo (Aeneas.Std.Repr.pointer U32) destination destinationBase word ∗
          pointsTo (Aeneas.Std.Repr.pointer U32) source sourceBase word) h) s₀ := by
  rintro h F ⟨owned, slots, parts, rfl, owner, saved⟩ hd hm hi
  obtain ⟨ownerFrame, slotsFrame⟩ := Fragment.disjoint_union_left.mp hd
  rw [Fragment.union_assoc] at hm
  unfold copy_after_deallocation_tail
  apply HeapWP.Spec.bind (HeapWP.dealloc.spec raw_box.u32Repr word word.address value s₀
    (by decide) authority owned (slots ∪ F) owner
    (Fragment.disjoint_union_right.mpr ⟨parts, ownerFrame⟩) hm hi)
  rintro _ s₁ ⟨empty, _, hm₁, hi₁, rfl⟩
  have matching : Fragment.Matches s₁ (slots ∪ F) := by simpa using hm₁
  apply HeapWP.Spec.bind (copy_stored_pointer.spec source destination sourceBase
    destinationBase word old 0 slots F s₁ saved slotsFrame matching hi₁)
  rintro copied s₂ ⟨h₂, hd₂, hm₂, hi₂, rfl, hp₂⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h₂, hd₂, hm₂, hi₂, rfl, rfl, hp₂⟩

end raw_memory_views
