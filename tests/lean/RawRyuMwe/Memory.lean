module

public import RawMemoryViews.ByteStorage
public import RawMemoryViews.Repr
public import RawMemoryViews.ByteLayout
public import Aeneas.Std.Heap.Step
public import Aeneas.Std.Heap.Copy
public import Aeneas.Std.Heap.PointerOps
public import Aeneas.Std.Heap.PointerMovement
import all Aeneas.Std.Core.PtrOps
import all RawBoxProofs
import all Aeneas.Std.Heap.Resources

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace scalar_mwe

/- Target calibration is explicit: these codecs describe little-endian scalars.
   The Rust tests use to_ne_bytes so they do not assume little-endian hosts. -/
def codec (encode : T → Vector U8 n) (decode : Vector U8 n → T)
    (roundtrip : ∀ x, decode (encode x) = x)
    (align : Alignment) (aligned : align.val ∣ n) : Aeneas.Std.Repr T where
  size := n
  align := align
  aligned := aligned
  decode bytes := (bytes.mapM Byte.numeric).map decode
  encode value bytes := bytes = (encode value).map Byte.data
  encode_complete value := ⟨_, rfl⟩
  encode_decode value bytes h := by
    subst bytes
    rw [raw_box.dataBytes_numeric]
    simp only [Option.map_some, roundtrip]
  decode_mono bytes bytes' value decoded agree := by
    cases hn : bytes.mapM Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      simpa only [raw_box.numericBytes_eq bytes bytes' values hn agree] using decoded
  encode_valid value bytes i h := by
    subst bytes
    simp

def bytes64 (x : U64) := raw_memory_views.addressBytes x.bv
def bytes16 := raw_memory_views.u16Bytes

def u64Repr : Aeneas.Std.Repr U64 :=
  codec bytes64 (fun bytes => ⟨raw_memory_views.decodeAddress bytes⟩)
    (fun x => congrArg UScalar.mk (raw_memory_views.decodeAddress_addressBytes x.bv))
    ⟨8, 3, rfl⟩ (by decide)

def u16Repr : Aeneas.Std.Repr U16 :=
  codec bytes16 (fun bytes => ⟨bytes[1].bv ++ bytes[0].bv⟩)
    (fun x => congrArg UScalar.mk (raw_memory_views.u16Bytes_roundtrip x))
    ⟨2, 1, rfl⟩ (by decide)

theorem codec_noPointers (enc : T → Vector U8 n) (dec : Vector U8 n → T)
    (rt : ∀ x, dec (enc x) = x) (align : Alignment) (ha : align.val ∣ n)
    (x : T) (p : RawPtr Unit) : ¬ (codec enc dec rt align ha).Carries x p := by
  rintro ⟨data, encoded, i, lane, hp⟩
  change data = (enc x).map Byte.data at encoded
  subst data
  have impossible := (Vector.getElem_map Byte.data (xs := enc x) i.isLt).symm.trans hp
  cases impossible

theorem u64_noPointers (x : U64) (p : RawPtr Unit) : ¬ u64Repr.Carries x p :=
  codec_noPointers _ _ _ _ _ x p

theorem u16_noPointers (x : U16) (p : RawPtr Unit) : ¬ u16Repr.Carries x p :=
  codec_noPointers _ _ _ _ _ x p

/-- Byte-level footprint: it does not assert that the bytes decode as any T. -/
abbrev bytesAt (p : RawPtr U8) (base : BasePtr) (bytes : List Aeneas.Std.Byte) (depth : Nat := 0) :=
  block Repr.u8 p base (bytes.map (Cell.shared depth))

theorem unaligned_bytes (repr : Aeneas.Std.Repr T) (enc : T → Vector U8 repr.size)
    (encoding : ∀ x data, repr.encode x data ↔ data = (enc x).map Byte.data)
    (p : RawPtr U8) (base : BasePtr) (value : T) (depth : Nat) :
    pointsTo repr.unaligned (p.cast T) base value depth =
      bytesAt p base ((enc value).toList.map Byte.data) depth := by
  funext h
  apply propext
  simp only [pointsTo, Repr.unaligned, encoding, exists_eq_left]
  simp [block, bytesAt, RawPtr.cast, RawPtr.offsetFrom, Repr.u8, Vector.toList_map]

end scalar_mwe
