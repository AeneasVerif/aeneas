module

public import RawBoxProofs
import all RawBoxProofs
import all Aeneas.Std.Heap.Repr

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_memory_views

def addressBytes (bits : BitVec 64) : Vector U8 8 :=
  Vector.ofFn fun i => ⟨bits.extractLsb' (8 * i.val) 8⟩

def decodeAddress (bytes : Vector U8 8) : BitVec 64 :=
  bytes[7].bv ++ bytes[6].bv ++ bytes[5].bv ++ bytes[4].bv ++
    bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv

theorem decodeAddress_addressBytes (bits : BitVec 64) :
    decodeAddress (addressBytes bits) = bits := by
  change bits.extractLsb' 56 8 ++ bits.extractLsb' 48 8 ++
    bits.extractLsb' 40 8 ++ bits.extractLsb' 32 8 ++
    bits.extractLsb' 24 8 ++ bits.extractLsb' 16 8 ++
    bits.extractLsb' 8 8 ++ bits.extractLsb' 0 8 = bits
  bv_tac 64

/-- The prototype's thin-pointer ABI has eight little-endian lanes. The explicit
    width premise calibrates the integer read to that ABI, not to an arbitrary target. -/
def usizeRepr (h64 : UScalarTy.numBits .Usize = 64) : Aeneas.Std.Repr Usize where
  size := 8
  align := ⟨8, 3, rfl⟩
  aligned := by decide
  decode bytes := do
    let values ← bytes.mapM Aeneas.Std.Byte.numeric
    pure ⟨(decodeAddress values).cast h64.symm⟩
  encode value bytes :=
    bytes = (addressBytes (value.bv.cast h64)).map Aeneas.Std.Byte.data
  encode_complete value := ⟨_, rfl⟩
  encode_decode value bytes encoded := by
    subst bytes
    rw [raw_box.dataBytes_numeric]
    simp [decodeAddress_addressBytes]
  decode_mono bytes bytes' value decoded agree := by
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      have same := raw_box.numericBytes_eq bytes bytes' values hn agree
      simpa only [same] using decoded
  encode_valid value bytes i encoded := by
    subst bytes
    simp

private theorem pointer_lane_numeric (h64 : UScalarTy.numBits .Usize = 64)
    (p : RawPtr T) (i : Fin 8) :
    Aeneas.Std.Byte.numeric (.pointer (p.cast Unit) i.val) =
      some (addressBytes (p.address.bv.cast h64))[i.val] := by
  simp only [Aeneas.Std.Byte.numeric, pointerWidth, i.isLt, ↓reduceIte,
    addressBytes, Vector.getElem_ofFn, RawPtr.cast]
  apply congrArg some
  apply UScalar.eq_of_val_eq
  change (BitVec.ofNat 8 (p.address.val / 2 ^ (8 * i.val))).toNat =
    ((p.address.bv.cast h64).extractLsb' (8 * i.val) 8).toNat
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_cast,
    Nat.shiftRight_eq_div_pow, UScalar.bv_toNat]

theorem pointer_numeric (h64 : UScalarTy.numBits .Usize = 64) (p : RawPtr T) :
    (Aeneas.Std.Repr.pointerEncoding p).mapM Aeneas.Std.Byte.numeric =
      some (addressBytes (p.address.bv.cast h64)) := by
  let indices : Vector (Fin 8) 8 := Vector.ofFn id
  have encoded : Aeneas.Std.Repr.pointerEncoding p =
      indices.map (fun i => Aeneas.Std.Byte.pointer (p.cast Unit) i.val) := by
    ext i hi
    simp [Aeneas.Std.Repr.pointerEncoding, indices]
  rw [encoded, Vector.mapM_map]
  simp only [Function.comp_def]
  have numeric : (fun i : Fin 8 => Aeneas.Std.Byte.numeric (.pointer (p.cast Unit) i.val)) =
      (fun i => pure ((addressBytes (p.address.bv.cast h64))[i.val])) :=
    funext (pointer_lane_numeric h64 p)
  rw [numeric, Vector.mapM_pure]
  simp [indices]

theorem usizeRepr_pointer (h64 : UScalarTy.numBits .Usize = 64) (p : RawPtr T) :
    (usizeRepr h64).decode (Aeneas.Std.Repr.pointerEncoding p) = some p.address := by
  change ((Aeneas.Std.Repr.pointerEncoding p).mapM Aeneas.Std.Byte.numeric).bind _ = _
  rw [pointer_numeric h64 p]
  simp [decodeAddress_addressBytes]

end raw_memory_views
