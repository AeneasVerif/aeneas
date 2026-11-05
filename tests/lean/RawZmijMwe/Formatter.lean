module

public import RawZmijMwe.Decimal
public import RawRyuMwe.Storage
import all Aeneas.Std.Heap.Resources

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_zmij_mwe

set_option maxHeartbeats 1000000

theorem decimalDigits_length (value : U8) :
    0 < (decimalDigits value).length ∧ (decimalDigits value).length ≤ 3 := by
  unfold decimalDigits
  split
  · simp
  · split
    · simp
    · simp

def formattedBytes (old : Vector Aeneas.Std.Byte 4) (value : U8) : List Aeneas.Std.Byte :=
  (decimalDigits value).map Byte.data ++ old.toList.drop (decimalDigits value).length

@[simp]
theorem formattedBytes_length (old : Vector Aeneas.Std.Byte 4) (value : U8) :
    (formattedBytes old value).length = 4 := by
  have bounds := decimalDigits_length value
  simp only [formattedBytes, List.length_append, List.length_map,
    List.length_drop, Vector.length_toList]
  agrind

theorem write_decimal.storage_spec (out : RawPtr U8) (value : U8)
    (old : Vector Aeneas.Std.Byte 4) :
    HeapWP.Triple (storageAt out old.toList 0) (write_decimal out value)
      (fun finish h => finish.provenance = out.provenance ∧
        finish.address.val = out.address.val + (decimalDigits value).length ∧
        storageAt out (formattedBytes old value) 0 h) := by
  apply HeapWP.Triple.conseq (P' := bytesAt out out.address old.toList ∗
      alloc Repr.u8 out out.address 4 false)
    (Q' := fun finish => (fun h => finish.provenance = out.provenance ∧
      finish.address.val = out.address.val + (decimalDigits value).length ∧
      bytesAt out out.address (formattedBytes old value) 0 h) ∗
        alloc Repr.u8 out out.address 4 false)
  · intro h hp
    apply (sep_comm _ _ h).mp
    simpa only [storageAt, Vector.length_toList] using hp
  · rintro finish h ⟨a, b, hd, rfl, ⟨prov, addr, cells⟩, cleanup⟩
    refine ⟨prov, addr, b, a, hd.symm, Fragment.union_comm _ _, ?_, cells⟩
    simpa using cleanup
  · exact HeapWP.frame (write_decimal.spec out value out.address old)

/- Local raw-storage adapters for the anticipated forward/backward interface.
   These are not compiler emissions or ordinary typed MaybeUninit descriptors. -/
def DecimalBuffer.as_mut_ptr_back (p : RawPtr U8) (size : Nat) :
    Result (List Aeneas.Std.Byte) := do
  let updated ← snapshotBytes p
  closeBytes p size 0
  .ok updated

def DecimalBuffer.as_mut_ptr (bytes : List Aeneas.Std.Byte) (address : BasePtr) :
    Result (RawPtr U8 × Result (List Aeneas.Std.Byte)) := do
  let p ← exposeBytes bytes 0 address
  .ok (p, as_mut_ptr_back p bytes.length)

def DecimalBuffer.as_ptr (bytes : List Aeneas.Std.Byte) (address : BasePtr) :
    Result (RawPtr U8 × Result Unit) := do
  let p ← exposeBytes bytes 1 address
  .ok (p, closeBytes p bytes.length 1)

/- The three placements are ghost parameters for the user's ad hoc hypothesis.
   Every exposure returns its matching backward computation and a fresh view ID.
   All heap borrows end before returning the pure slice value; the outer backward
   computation only returns updated storage. This is handwritten, not emitted. -/
def DecimalBuffer.format (old : Vector Aeneas.Std.Byte 4) (value : U8)
    (mutableAddress firstSharedAddress secondSharedAddress : BasePtr) :
    Result (Slice U8 × Result (List Aeneas.Std.Byte)) := do
  let (start, start_back) ← as_mut_ptr old.toList mutableAddress
  let finish ← write_decimal start value
  let updated ← start_back
  let (origin, origin_back) ← as_ptr updated firstSharedAddress
  let distance ← RawPtr.offset_from Repr.u8 finish origin
  origin_back
  let len := IScalar.hcast .Usize distance
  let (ptr, ptr_back) ← as_ptr updated secondSharedAddress
  let (bytes, bytes_back) ← core.slice.raw.from_raw_parts Repr.u8 ptr len
  bytes_back
  ptr_back
  .ok (bytes, .ok updated)

/-- **Spec theorem for `raw_zmij_mwe::DecimalBuffer::format`**
    Conditional on address stability, the pure slice is exactly the decimal
    output. All heap borrows end before returning; the trivial backward
    computation returns updated raw storage and preserves every external frame. -/
theorem DecimalBuffer.format.spec (old : Vector Aeneas.Std.Byte 4) (value : U8)
    (mutableAddress firstSharedAddress secondSharedAddress : BasePtr)
    (sameAddress : mutableAddress = firstSharedAddress)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (DecimalBuffer.format old value mutableAddress firstSharedAddress secondSharedAddress)
      (fun result s₁ => result.1.val = decimalDigits value ∧
        HeapWP.Spec result.2 (fun updated s₂ =>
          updated = formattedBytes old value ∧ s₂.Inv ∧ Fragment.Matches s₂ F) s₁) s₀ := by
  simp only [DecimalBuffer.format, DecimalBuffer.as_mut_ptr, DecimalBuffer.as_mut_ptr_back,
    DecimalBuffer.as_ptr, Std.bind_assoc, bind_ok,
    uncurry_apply_pair, Vector.length_toList]
  apply HeapWP.Spec.bind (exposeBytes.spec old.toList 0 mutableAddress s₀ F hi hm)
  rintro start s₁ ⟨startAddr, _, h₁, hd₁, hm₁, hi₁, hp₁⟩
  apply HeapWP.Spec.bind (write_decimal.storage_spec start value old h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
  rintro finish s₂ ⟨h₂, hd₂, hm₂, hi₂, prov, cursor, hp₂⟩
  apply HeapWP.Spec.bind (snapshotBytes.spec start (formattedBytes old value) 0 h₂ F s₂ hp₂ hm₂)
  rintro updated s₃ ⟨updatedEq, stateEq⟩
  subst updated
  subst s₃
  have closing := closeBytes.state_spec start (formattedBytes old value) 0 h₂ F s₂ hp₂ hd₂ hm₂ hi₂
  simp only [formattedBytes_length] at closing
  apply HeapWP.Spec.bind closing
  rintro _ s₃ ⟨hi₃, hm₃, retainedStart, _⟩
  apply HeapWP.Spec.bind (exposeBytes.spec (formattedBytes old value) 1 firstSharedAddress s₃ F hi₃ hm₃)
  rintro origin s₄ ⟨originAddr, preserves, h₄, hd₄, hm₄, hi₄, hp₄⟩
  obtain ⟨a, ha, abase, alen, alive⟩ := preserves start 4 retainedStart
  obtain ⟨b, hb, blive, bbase, _, brepr, _⟩ :=
    whole_storage origin (formattedBytes old value) 1 h₄ s₄ hp₄
      ((Fragment.matches_union _ _ _).mp hm₄).1
  have blen : b.repr.length = 4 := by simp [brepr]
  have balive := Heap.allocationAlive_of_live s₄ b blive
  have equalStarts : start.address = origin.address := startAddr.trans (sameAddress.trans originAddr.symm)
  have bounds := decimalDigits_length value
  have afits : (decimalDigits value).length ≤ a.repr.length := by agrind
  have signedFits : ((decimalDigits value).length : Int) ≤ IScalar.cMax .Isize := by scalar_tac
  apply HeapWP.Spec.bind
    (HeapWP.offset_from_reexposed.spec start finish origin (decimalDigits value).length
      s₄ a b hi₄ ha hb alive balive abase.symm bbase.symm equalStarts
      (by agrind) (by agrind) prov cursor afits signedFits)
  rintro distance s₅ ⟨distanceVal, stateEq⟩
  subst s₅
  have lenEq : (IScalar.hcast .Usize distance).val = (decimalDigits value).length := by
    have castBounds : 0 ≤ distance.val ∧ distance.val ≤ UScalar.max .Usize := by scalar_tac
    have castEq := IScalar.hcast_inBounds_spec .Usize distance castBounds
    simp only [lift, WP.spec_ok, distanceVal] at castEq
    exact_mod_cast castEq
  apply HeapWP.Spec.bind
    (closeBytes.state_spec origin (formattedBytes old value) 1 h₄ F s₄ hp₄ hd₄ hm₄ hi₄)
  rintro _ s₅ ⟨hi₅, hm₅, _, _⟩
  apply HeapWP.Spec.bind
    (exposeBytes.spec (formattedBytes old value) 1 secondSharedAddress s₅ F hi₅ hm₅)
  rintro ptr s₆ ⟨_, _, h₆, hd₆, hm₆, hi₆, hp₆⟩
  obtain ⟨cleanup, cells, disjoint, union, alloc, raw⟩ := hp₆
  have hcells : cells.Disjoint (cleanup ∪ F) :=
    Fragment.disjoint_union_right.mpr ⟨disjoint.symm,
      (Fragment.disjoint_union_left.mp (union ▸ hd₆)).2⟩
  have matching : Fragment.Matches s₆ (cells ∪ (cleanup ∪ F)) := by
    rw [union, Fragment.union_assoc] at hm₆
    simpa [Fragment.matches_union, and_left_comm, and_assoc] using hm₆
  let digits : Vector U8 (decimalDigits value).length := ⟨(decimalDigits value).toArray, by simp⟩
  apply HeapWP.Spec.bind (borrow_prefix.spec ptr ptr.address digits
    (old.toList.drop (decimalDigits value).length) 1 (IScalar.hcast .Usize distance)
      lenEq bounds.1 cells (cleanup ∪ F) s₆ raw hcells matching hi₆)
  rintro ⟨bytes, back⟩ s₇ ⟨contents, returning⟩
  dsimp only [Aeneas.Std.uncurry]
  apply HeapWP.Spec.bind returning
  rintro _ s₈ stateEq
  subst s₈
  have hp₆ : storageAt ptr (formattedBytes old value) 1 h₆ :=
    ⟨cleanup, cells, disjoint, union, alloc, raw⟩
  apply HeapWP.Spec.bind
    (closeBytes.state_spec ptr (formattedBytes old value) 1 h₆ F s₆ hp₆ hd₆ hm₆ hi₆)
  rintro _ s₈ ⟨hi₈, hm₈, _, _⟩
  apply (HeapWP.Spec.pure _ _ _).mpr
  refine ⟨by simpa [digits] using contents, ?_⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, hi₈, hm₈⟩

/- Collect the pure updated storage for composing repeated formatter calls.
   The formatter has already executed all heap-borrow returns. -/
def DecimalBuffer.format_and_return (old : Vector Aeneas.Std.Byte 4) (value : U8)
    (address : BasePtr) : Result (Slice U8 × List Aeneas.Std.Byte) := do
  let (bytes, back) ← DecimalBuffer.format old value address address address
  let updated ← back
  pure (bytes, updated)

/-- **Spec theorem for one complete `DecimalBuffer::format` borrow scope**
    All exposures use the hypothesized stable address, but still issue fresh IDs. -/
@[step]
theorem DecimalBuffer.format_and_return.spec (old : Vector Aeneas.Std.Byte 4)
    (value : U8) (address : BasePtr) :
    ⦃ SepLogic.empty ⦄ DecimalBuffer.format_and_return old value address
    ⦃ (bytes : Slice U8) (updated : List Aeneas.Std.Byte) => fun h =>
      bytes.val = decimalDigits value ∧ updated = formattedBytes old value ∧ SepLogic.empty h ⦄ := by
  intro h F s₀ empty hd hm hi
  subst h
  unfold DecimalBuffer.format_and_return
  apply HeapWP.Spec.bind
    (DecimalBuffer.format.spec old value address address address rfl F s₀ (by simpa using hm) hi)
  rintro ⟨bytes, back⟩ s₁ ⟨contents, returning⟩
  dsimp only [Aeneas.Std.uncurry]
  apply HeapWP.Spec.bind returning
  rintro updated s₂ ⟨updatedEq, hi₂, hm₂⟩
  apply (HeapWP.Spec.pure _ _ _).mpr
  exact ⟨∅, Fragment.disjoint_empty_left F, by simpa using hm₂, hi₂, contents, updatedEq, rfl⟩

end raw_zmij_mwe
