module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Heap
public import Aeneas.Data.BitVec
@[expose] public section

/-!
# Byte representations of scalars

Scalars are stored in the heap as their little-endian bytes.  Decoding accepts
exactly `numBits / 8` bytes, so a run of bytes decodes to at most one scalar of
each type, and any run of the right length decodes to some scalar: reading a
scalar through a pointer of another scalar type of the same size is defined.
A scalar is aligned to its size, which is at least as strict as Rust's alignment
of integers.
-/

namespace Aeneas.Std

theorem UScalarTy.numBits_mod_eight (ty : UScalarTy) : ty.numBits % 8 = 0 := by
  cases ty <;> simp only [UScalarTy.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem IScalarTy.numBits_mod_eight (ty : IScalarTy) : ty.numBits % 8 = 0 := by
  cases ty <;> simp only [IScalarTy.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

instance UScalar.instByteRepr (ty : UScalarTy) : ByteRepr (UScalar ty) where
  size := ty.numBits / 8
  align := ty.numBits / 8
  align_dvd_size := Nat.dvd_refl _
  encode x := x.bv.toLEBytes
  decode bytes := (BitVec.decodeLE ty.numBits bytes).map UScalar.mk
  length_encode x := by
    have := ty.numBits_mod_eight
    simp only [BitVec.toLEBytes_length]
    omega
  decode_encode x := by
    simp only [BitVec.decodeLE_toLEBytes ty.numBits_mod_eight, Option.map_some]
  encode_of_decode {bytes x} hDecode := by
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hDecode
    exact BitVec.toLEBytes_of_decodeLE hb

instance IScalar.instByteRepr (ty : IScalarTy) : ByteRepr (IScalar ty) where
  size := ty.numBits / 8
  align := ty.numBits / 8
  align_dvd_size := Nat.dvd_refl _
  encode x := x.bv.toLEBytes
  decode bytes := (BitVec.decodeLE ty.numBits bytes).map IScalar.mk
  length_encode x := by
    have := ty.numBits_mod_eight
    simp only [BitVec.toLEBytes_length]
    omega
  decode_encode x := by
    simp only [BitVec.decodeLE_toLEBytes ty.numBits_mod_eight, Option.map_some]
  encode_of_decode {bytes x} hDecode := by
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hDecode
    exact BitVec.toLEBytes_of_decodeLE hb

@[simp] theorem UScalar.byteRepr_size (ty : UScalarTy) :
    ByteRepr.size (UScalar ty) = ty.numBits / 8 := rfl

@[simp] theorem UScalar.byteRepr_align (ty : UScalarTy) :
    ByteRepr.align (UScalar ty) = ty.numBits / 8 := rfl

@[simp] theorem IScalar.byteRepr_size (ty : IScalarTy) :
    ByteRepr.size (IScalar ty) = ty.numBits / 8 := rfl

@[simp] theorem IScalar.byteRepr_align (ty : IScalarTy) :
    ByteRepr.align (IScalar ty) = ty.numBits / 8 := rfl

@[simp] theorem UScalar.encode_eq {ty : UScalarTy} (x : UScalar ty) :
    ByteRepr.encode x = x.bv.toLEBytes := rfl

@[simp] theorem IScalar.encode_eq {ty : IScalarTy} (x : IScalar ty) :
    ByteRepr.encode x = x.bv.toLEBytes := rfl

theorem UScalar.byteRepr_size_pos (ty : UScalarTy) : 0 < ByteRepr.size (UScalar ty) := by
  cases ty <;> simp only [UScalar.byteRepr_size, UScalarTy.numBits] <;>
    rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem IScalar.byteRepr_size_pos (ty : IScalarTy) : 0 < ByteRepr.size (IScalar ty) := by
  cases ty <;> simp only [IScalar.byteRepr_size, IScalarTy.numBits] <;>
    rcases System.Platform.numBits_eq with h | h <;> simp [h]

/-- Bytes stored as `u8`s encode to themselves. -/
@[simp] theorem UScalar.flatMap_encode_u8 (bytes : List Byte) :
    (bytes.map (UScalar.mk (ty := .U8))).flatMap ByteRepr.encode = bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]
      exact congrArg (· ++ rest) (BitVec.toLEBytes_byte b)

theorem UScalar.map_mk_flatMap_encode_u8 (values : List U8) :
    (values.flatMap ByteRepr.encode).map (UScalar.mk (ty := .U8)) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    rw [List.flatMap_cons, UScalar.encode_eq, BitVec.toLEBytes_byte, List.map_append, ih]
    rfl

/-! ## Reinterpreting a scalar as a scalar of the same size -/

@[simp] theorem UScalar.decode_encode_uscalar {ty ty' : UScalarTy} (x : UScalar ty)
    (h : ty.numBits = ty'.numBits) :
    ByteRepr.decode (α := UScalar ty') x.bv.toLEBytes = some ⟨x.bv.cast h⟩ := by
  change (BitVec.decodeLE ty'.numBits x.bv.toLEBytes).map UScalar.mk = _
  rw [← BitVec.toLEBytes_cast h x.bv, BitVec.decodeLE_toLEBytes ty'.numBits_mod_eight]
  rfl

@[simp] theorem UScalar.decode_encode_iscalar {ty : UScalarTy} {ty' : IScalarTy}
    (x : UScalar ty) (h : ty.numBits = ty'.numBits) :
    ByteRepr.decode (α := IScalar ty') x.bv.toLEBytes = some ⟨x.bv.cast h⟩ := by
  change (BitVec.decodeLE ty'.numBits x.bv.toLEBytes).map IScalar.mk = _
  rw [← BitVec.toLEBytes_cast h x.bv, BitVec.decodeLE_toLEBytes ty'.numBits_mod_eight]
  rfl

@[simp] theorem IScalar.decode_encode_uscalar {ty : IScalarTy} {ty' : UScalarTy}
    (x : IScalar ty) (h : ty.numBits = ty'.numBits) :
    ByteRepr.decode (α := UScalar ty') x.bv.toLEBytes = some ⟨x.bv.cast h⟩ := by
  change (BitVec.decodeLE ty'.numBits x.bv.toLEBytes).map UScalar.mk = _
  rw [← BitVec.toLEBytes_cast h x.bv, BitVec.decodeLE_toLEBytes ty'.numBits_mod_eight]
  rfl

@[simp] theorem IScalar.decode_encode_iscalar {ty ty' : IScalarTy} (x : IScalar ty)
    (h : ty.numBits = ty'.numBits) :
    ByteRepr.decode (α := IScalar ty') x.bv.toLEBytes = some ⟨x.bv.cast h⟩ := by
  change (BitVec.decodeLE ty'.numBits x.bv.toLEBytes).map IScalar.mk = _
  rw [← BitVec.toLEBytes_cast h x.bv, BitVec.decodeLE_toLEBytes ty'.numBits_mod_eight]
  rfl

end Aeneas.Std
