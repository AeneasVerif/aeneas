module

public import RawRyuMwe.Memory
public import Aeneas.Std.Heap.ByteWindows
public import Aeneas.Std.Heap.ByteCopy
import all Aeneas.Std.Core.PtrOps
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace scalar_mwe

theorem write_window.spec (repr : Aeneas.Std.Repr T) (enc : T → Vector U8 repr.size)
    (encoding : ∀ x data, repr.encode x data ↔ data = (enc x).map Byte.data)
    (p q : RawPtr U8) (base : BasePtr) (old : List Aeneas.Std.Byte) (start : Nat)
    (value : T) (bound : start + repr.size ≤ old.length) (positive : 0 < repr.size)
    (noPointers : ∀ r, ¬ repr.Carries value r)
    (prov : q.provenance = p.provenance) (address : q.address.val = p.address.val + start) :
    ⦃ bytesAt p base old ⦄ RawPtr.write_unaligned repr (q.cast T) value
    ⦃ _ => bytesAt p base
      (old.take start ++ (enc value).toList.map Byte.data ++ old.drop (start + repr.size)) ⦄ := by
  let bytes : Vector Aeneas.Std.Byte repr.size :=
    ⟨((old.drop start).take repr.size).toArray, by simp; agrind⟩
  have localWrite := HeapWP.write_unaligned.spec repr (q.cast T) base bytes value noPointers positive
  have pre :
      block repr.unaligned (q.cast T) base (bytes.map (Cell.shared 0)).toList =
        block Repr.u8 q base (((old.map (Cell.shared 0)).drop start).take repr.size) := by
    funext h
    simp [block, Repr.unaligned, Repr.u8, RawPtr.cast, RawPtr.offsetFrom, bytes,
      List.map_drop, List.map_take]
  rw [pre, unaligned_bytes repr enc encoding q base value 0] at localWrite
  have result := HeapWP.replace_window.spec p q base (old.map (Cell.shared 0))
    (((enc value).toList.map Byte.data).map (Cell.shared 0)) start repr.size
    (by simpa using bound) (by simp) prov address _ localWrite
  simpa only [bytesAt, List.map_append, List.map_take, List.map_drop] using result

/-- Byte-pointer addition is justified by the existing region, including its
    uninitialized suffix. The address-fit fact follows from heap validity. -/
theorem add_bytes.spec (p : RawPtr U8) (base : BasePtr) (old : List Aeneas.Std.Byte)
    (offset : Usize) (bound : offset.val < old.length) :
    ⦃ bytesAt p base old ⦄ RawPtr.add Repr.u8 p offset
    ⦃ (q : RawPtr U8) => fun h =>
      q.provenance = p.provenance ∧ q.address.val = p.address.val + offset.val ∧
      bytesAt p base old 0 h ⦄ := by
  intro h F s hp hd hm hi
  let bytes : Vector Aeneas.Std.Byte old.length := ⟨old.toArray, by simp⟩
  have hp' : raw_memory_views.writableBytes p base bytes h := by
    simpa [bytes, raw_memory_views.writableBytes, bytesAt, Vector.toList_map] using hp
  have fits := raw_memory_views.writableBytes_fits p base bytes h s hp'
    ((Fragment.matches_union _ _ _).mp hm).1 hi offset.val bound
  simpa [bytes, raw_memory_views.writableBytes, bytesAt, Vector.toList_map] using
    raw_memory_views.add_writable.spec p base bytes offset (by agrind) (by agrind) fits
      h F s hp' hd hm hi

theorem advance_bytes.spec (start p : RawPtr U8) (base : BasePtr)
    (old : Vector Aeneas.Std.Byte n) (offset : Nat)
    (prov : p.provenance = start.provenance)
    (address : p.address.val = start.address.val + offset) (bound : offset + 1 < n) :
    ⦃ bytesAt start base old.toList ⦄ RawPtr.add Repr.u8 p 1#usize
    ⦃ (q : RawPtr U8) => fun h =>
      q.provenance = start.provenance ∧ q.address.val = start.address.val + (offset + 1) ∧
      bytesAt start base old.toList 0 h ⦄ := by
  apply HeapWP.Triple.checkedModify
  intro h F s hp hd hm hi
  have keep := hp
  have writable : raw_memory_views.writableBytes start base old h := by
    simpa [raw_memory_views.writableBytes, bytesAt, Vector.toList_map] using hp
  have matching := ((Fragment.matches_union _ _ _).mp hm).1
  have fits := raw_memory_views.writableBytes_fits start base old h s writable matching hi
    (offset + 1) bound
  obtain ⟨lower, _, cells⟩ := hp
  rw [cells] at matching
  have size : (Repr.u8.region n).size = n := by simp [Repr.region, Repr.u8]
  obtain ⟨blk, hb, hl, live, baseEq, _⟩ :=
    bytes_of_matches (s := s) (bptr := base) (repr := Repr.u8.region n)
      (p := start.cast Unit) (data := (old.map (Cell.shared 0)).cast size.symm)
      (by simp only [size]; agrind)
      (by simpa [RawPtr.cast, RawPtr.offsetFrom, Vector.toList_map, Vector.toList_cast] using matching)
  simp only [size, RawPtr.offsetFrom, RawPtr.cast] at hb
  change s.allocations start.provenance = some blk at hl
  have startBound : base.val ≤ p.address.val ∧ p.address.val ≤ base.val + blk.repr.length := by
    scalar_tac
  have finishBound : (base.val : Int) ≤ (p.address.val : Int) + 1 ∧
      (p.address.val : Int) + 1 ≤ base.val + blk.repr.length := by scalar_tac
  have fit : (p.address.val : Int) + 1 < (2 : Int) ^ System.Platform.numBits := by
    simp only [address, Nat.cast_add] at *
    exact_mod_cast fits
  let q : RawPtr U8 := ⟨start.provenance,
    ⟨BitVec.ofNat _ (start.address.val + (offset + 1))⟩⟩
  have qaddr : q.address.val = start.address.val + (offset + 1) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  have run : Heap.offset Repr.u8 p (1#usize).val s = some q := by
    have nat : ((p.address.val : Int) + 1).toNat = start.address.val + (offset + 1) := by
      rw [address]
      norm_cast
    simp [Heap.offset, Repr.u8, hl, live, baseEq, startBound, finishBound,
      fit, nat, q, prov]
  refine ⟨⟨q, s, run, rfl⟩, ?_⟩
  rintro result s₁ ⟨run₁, rfl⟩
  have eq := Option.some.inj (run₁.symm.trans run)
  subst result
  exact ⟨h, hd, hm, hi, rfl, qaddr, keep⟩

def write_at (repr : Aeneas.Std.Repr T) (p : RawPtr U8) (offset : Usize) (value : T) :
    Result Unit := do
  let q ← RawPtr.add Repr.u8 p offset
  RawPtr.write_unaligned repr (q.cast T) value

theorem write_at.spec (repr : Aeneas.Std.Repr T) (enc : T → Vector U8 repr.size)
    (encoding : ∀ x data, repr.encode x data ↔ data = (enc x).map Byte.data)
    (p : RawPtr U8) (base : BasePtr) (old : List Aeneas.Std.Byte) (offset : Usize)
    (value : T) (bound : offset.val + repr.size ≤ old.length) (positive : 0 < repr.size)
    (noPointers : ∀ r, ¬ repr.Carries value r) :
    ⦃ bytesAt p base old ⦄ write_at repr p offset value
    ⦃ _ => bytesAt p base
      (old.take offset.val ++ (enc value).toList.map Byte.data ++
        old.drop (offset.val + repr.size)) ⦄ := by
  unfold write_at
  apply HeapWP.Triple.bind (add_bytes.spec p base old offset (by agrind))
  intro q
  apply HeapWP.Triple.pure_pre
  intro prov
  apply HeapWP.Triple.pure_pre
  intro address
  exact write_window.spec repr enc encoding p q base old offset.val value bound positive
    noPointers prov address

end scalar_mwe
