module

public import RawZmijMwe.Writes
public import RawRyuMwe.Copy

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe

namespace raw_zmij_mwe

def write_digits_scoped (buffer : Vector U8 10) (digits : U64) (address : BasePtr) :
    Result (Unit × List Aeneas.Std.Byte) :=
  withStorage (buffer.toList.map Byte.data) address (fun p => write_digits p digits)

/-- **Spec theorem for `raw_zmij_mwe::write_digits`** Full scoped byte-array wrapper. -/
theorem write_digits_scoped.spec (buffer : Vector U8 10) (digits : U64) (address : BasePtr)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (write_digits_scoped buffer digits address)
      (fun result s₁ => result.2 =
        (buffer.toList.take 1 ++ (bytes64 digits).toList ++ buffer.toList.drop 9).map Byte.data ∧
        s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  let old := buffer.map Byte.data
  let new := old.toList.take 1 ++ (bytes64 digits).toList.map Byte.data ++ old.toList.drop 9
  have len : new.length = old.toList.length := by simp [new, old]
  have body (p : RawPtr U8) (_ : p.address = address) :
      HeapWP.Triple (storageAt p old.toList 0) (write_digits p digits)
        (fun _ h => True ∧ storageAt p new 0 h) := by
    apply preserve_storage _ _ p _ (fun _ => True) len
    exact HeapWP.Triple.conseq (fun _ hp => hp) (fun _ _ hp => ⟨True.intro, hp⟩)
      (write_digits.spec p p.address old digits)
  have scopedRun := withStorage.spec old.toList new address _ (fun _ => True) len body F s₀ hm hi
  simp only [old, Vector.toList_map] at scopedRun
  unfold write_digits_scoped
  apply HeapWP.Spec.mono scopedRun
  rintro ⟨_, result⟩ s₁ ⟨_, rfl, hi₁, hm₁⟩
  exact ⟨by simp [new, old, Vector.toList_map], hi₁, hm₁⟩

def write_exponent_data (buffer : Vector U8 7) (data : U64)
    (sourceAddress destinationAddress : BasePtr) : Result (List Aeneas.Std.Byte) :=
  copy_scoped (bytes64 data).toList (buffer.toList.map Byte.data)
    sourceAddress destinationAddress 0#usize 1#usize 5

/-- **Spec theorem for `raw_zmij_mwe::write_exponent_data`**
    Copy only the first five native scalar bytes (little-endian here), retaining
    both neighbors. The source models `addr_of!(data).cast::<u8>()`. -/
theorem write_exponent_data.spec (buffer : Vector U8 7) (data : U64)
    (sourceAddress destinationAddress : BasePtr)
    (apart : sourceAddress.val + 8 ≤ destinationAddress.val ∨
      destinationAddress.val + 7 ≤ sourceAddress.val)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (write_exponent_data buffer data sourceAddress destinationAddress)
      (fun result s₁ => result =
        (buffer.toList.take 1 ++ (bytes64 data).toList.take 5 ++ buffer.toList.drop 6).map Byte.data ∧
        s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  have run := copy_scoped.spec (bytes64 data).toList (buffer.toList.map Byte.data)
    sourceAddress destinationAddress 0#usize 1#usize 5 (by decide)
    (by simp) (by simp) (by simp; agrind) F s₀ hm hi
  simpa [write_exponent_data, copiedBytes] using run

def write_exponent_scoped (buffer : Vector U8 5) (digits sign : U16) (overlap : Bool)
    (address : BasePtr) : Result (Unit × List Aeneas.Std.Byte) :=
  withStorage (buffer.toList.map Byte.data) address (fun p => write_exponent p digits sign overlap)

/-- **Spec theorem for `raw_zmij_mwe::write_exponent`**
    Full scoped wrapper, including the second-store-wins overlapping case. -/
theorem write_exponent_scoped.spec (buffer : Vector U8 5) (digits sign : U16) (overlap : Bool)
    (address : BasePtr) (F : Fragment) (s₀ : Heap)
    (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (write_exponent_scoped buffer digits sign overlap address)
      (fun result s₁ => result.2 = exponentBytes (buffer.toList.map Byte.data) digits sign overlap ∧
        s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  let old := buffer.map Byte.data
  let new := exponentBytes old.toList digits sign overlap
  have len : new.length = old.toList.length := by
    cases overlap
    · simp [new, exponentBytes, old]
    · simp [new, exponentBytes, old]
  have body (p : RawPtr U8) (_ : p.address = address) :
      HeapWP.Triple (storageAt p old.toList 0) (write_exponent p digits sign overlap)
        (fun _ h => True ∧ storageAt p new 0 h) := by
    apply preserve_storage _ _ p _ (fun _ => True) len
    exact HeapWP.Triple.conseq (fun _ hp => hp) (fun _ _ hp => ⟨True.intro, hp⟩)
      (write_exponent.spec p p.address old digits sign overlap)
  have scopedRun := withStorage.spec old.toList new address _ (fun _ => True) len body F s₀ hm hi
  simp only [old, Vector.toList_map] at scopedRun
  unfold write_exponent_scoped
  apply HeapWP.Spec.mono scopedRun
  rintro ⟨_, result⟩ s₁ ⟨_, rfl, hi₁, hm₁⟩
  exact ⟨by simp [new, old, Vector.toList_map], hi₁, hm₁⟩

end raw_zmij_mwe
