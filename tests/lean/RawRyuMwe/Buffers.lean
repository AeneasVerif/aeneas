module

public import RawRyuMwe.Readback
public import RawRyuMwe.Storage

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_ryu_mwe

def write_pair (p : RawPtr U8) (a b : U8) : Result Unit := do
  MutRawPtr.write Repr.u8 p a
  let q ← RawPtr.add Repr.u8 p 1#usize
  MutRawPtr.write Repr.u8 q b

@[step]
theorem write_pair.spec (p : RawPtr U8) (a b : U8) (base : BasePtr)
    (old : Vector Aeneas.Std.Byte 4) :
    ⦃ bytesAt p base old.toList ⦄ write_pair p a b
    ⦃ _ => bytesAt p base ([Byte.data a, Byte.data b] ++ old.toList.drop 2) ⦄ := by
  unfold write_pair
  have first := raw_memory_views.write_byte.spec p p base old ⟨0, by decide⟩ a rfl (by simp)
  simp only [raw_memory_views.writableBytes, Vector.toList_map] at first
  step with first
  step with add_bytes.spec p base (old.set 0 (.data a)).toList 1#usize (by simp)
    as ⟨q, _, prov, addr⟩
  have second := raw_memory_views.write_byte.spec p q base (old.set 0 (.data a))
    ⟨1, by decide⟩ b prov (by simpa using addr)
  simp only [raw_memory_views.writableBytes, Vector.toList_map] at second
  step with second
  · simp [Vector.toList_set, List.set_eq_take_append_cons_drop, bytesAt, List.map_drop] at *
    assumption

/- Both Rust cast spellings erase to the same transparent byte-pointer cast.
   The mutable view is returned before the fresh shared materialization. -/
def buffer_as (a b : U8) (mutableAddress sharedAddress : BasePtr) : Result (U8 × U8) := do
  let (_, updated) ← withStorage (List.replicate 4 Byte.uninit) mutableAddress
    (fun p => write_pair p a b)
  let p ← exposeBytes updated 1 sharedAddress
  let (bytes, back) ← core.slice.raw.from_raw_parts Repr.u8 p 2#usize
  let result ← read_two bytes
  back
  closeBytes p 4 1
  pure result

def buffer_cast := buffer_as

/-- **Spec theorem for `raw_ryu_mwe::buffer_as`**
    Two arbitrary input bytes survive both materializations; the uninitialized
    suffix is never read, and all actual return operations execute. -/
theorem buffer_as.spec (a b : U8) (mutableAddress sharedAddress : BasePtr)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (buffer_as a b mutableAddress sharedAddress)
      (fun result s₁ => result = (a, b) ∧ s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  let old : Vector Aeneas.Std.Byte 4 := Vector.replicate 4 .uninit
  let new : List Aeneas.Std.Byte := [Byte.data a, Byte.data b, .uninit, .uninit]
  have body (p : RawPtr U8) (_ : p.address = mutableAddress) :
      HeapWP.Triple (storageAt p (List.replicate 4 Byte.uninit) 0) (write_pair p a b)
        (fun _ h => True ∧ storageAt p new 0 h) := by
    apply preserve_storage _ _ p _ (fun _ => True) (by simp [new])
    have write := write_pair.spec p a b p.address old
    have run : HeapWP.Triple (bytesAt p p.address (List.replicate 4 Byte.uninit))
        (write_pair p a b) (fun _ => bytesAt p p.address new) := by
      simpa [old, new] using write
    exact HeapWP.Triple.conseq (fun _ hp => hp) (fun _ _ hp => ⟨True.intro, hp⟩) run
  unfold buffer_as
  apply HeapWP.Spec.bind (withStorage.spec _ new mutableAddress (fun p => write_pair p a b)
    (fun _ => True) (by simp [new]) body F s₀ hm hi)
  rintro ⟨_, updated⟩ s₁ ⟨_, updatedEq, hi₁, hm₁⟩
  dsimp only at updatedEq
  subst updated
  dsimp only [Aeneas.Std.uncurry]
  apply HeapWP.Spec.bind (exposeBytes.spec new 1 sharedAddress s₁ F hi₁ hm₁)
  rintro p s₂ ⟨_, _, h₂, hd₂, hm₂, hi₂, hp₂⟩
  obtain ⟨cleanup, cells, disjoint, union, alloc, raw⟩ := hp₂
  have cellsFrame : cells.Disjoint (cleanup ∪ F) :=
    Fragment.disjoint_union_right.mpr ⟨disjoint.symm, (Fragment.disjoint_union_left.mp (union ▸ hd₂)).2⟩
  have matching : Fragment.Matches s₂ (cells ∪ (cleanup ∪ F)) := by
    simp only [union, Fragment.matches_union] at hm₂ ⊢
    tauto
  apply HeapWP.Spec.bind (borrow_prefix.spec p p.address #v[a, b] [.uninit, .uninit] 1
    2#usize rfl (by decide) cells (cleanup ∪ F) s₂ raw cellsFrame matching hi₂)
  rintro ⟨bytes, back⟩ s₃ ⟨contents, returning⟩
  dsimp only [Aeneas.Std.uncurry]
  apply HeapWP.Spec.bind (HeapWP.Spec.of_spec (read_two.spec bytes a b contents) s₃)
  rintro ⟨x, y⟩ s₄ ⟨⟨rfl, rfl⟩, stateEq⟩
  subst s₄
  apply HeapWP.Spec.bind returning
  rintro _ s₄ stateEq
  subst s₄
  have closing := closeBytes.state_spec p new 1 h₂ F s₂
    ⟨cleanup, cells, disjoint, union, alloc, raw⟩ hd₂ hm₂ hi₂
  apply HeapWP.Spec.bind closing
  rintro _ s₄ ⟨hi₄, hm₄, _, _⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, hi₄, hm₄⟩

/-- **Spec theorem for `raw_ryu_mwe::buffer_cast`** Same byte-level semantics as `as`. -/
theorem buffer_cast.spec (a b : U8) (mutableAddress sharedAddress : BasePtr)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (buffer_cast a b mutableAddress sharedAddress)
      (fun result s₁ => result = (a, b) ∧ s₁.Inv ∧ Fragment.Matches s₁ F) s₀ :=
  buffer_as.spec a b mutableAddress sharedAddress F s₀ hm hi

end raw_ryu_mwe
