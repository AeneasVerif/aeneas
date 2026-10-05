module
public import Aeneas.Std.Scalar.ByteRepr
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.SliceDef
@[expose] public section

namespace Aeneas.Std

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

class IsScalar (T : Type) [ByteRepr T] : Prop where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

namespace IsScalar

def size {T : Type} [ByteRepr T] [IsScalar T] : Usize :=
  ⟨BitVec.ofNat _ (ByteRepr.size T)⟩

def numElems (T : Type) [ByteRepr T] [IsScalar T] (numBytes : Nat) : Nat :=
  (numBytes + (size (T := T)).val - 1) / (size (T := T)).val

def toBytes {T : Type} [ByteRepr T] [IsScalar T] (s : Slice T) : Result (Slice U8) :=
  let bytes := (s.val.flatMap ByteRepr.encode).map (UScalar.mk (ty := .U8))
  if h : bytes.length ≤ Usize.max then .ok (Slice.from bytes h)
  else .fail .arrayOutOfBounds

def fromBytes {T : Type} [ByteRepr T] [IsScalar T] (s : Slice U8) : Result (Slice T) :=
  match ByteRepr.decodeAll T (s.val.map UScalar.bv) with
  | none => .fail .undef
  | some values =>
    if h : values.length ≤ Usize.max then .ok (Slice.from values h)
    else .fail .arrayOutOfBounds

end IsScalar

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp

namespace IsScalar

theorem fromBytes_toBytes {T : Type} [ByteRepr T] [IsScalar T] (hSize : 0 < ByteRepr.size T)
    {s : Slice T} {bytes : Slice U8} (h : toBytes s = .ok bytes) : fromBytes bytes = .ok s := by
  simp only [toBytes] at h
  split at h
  · rw [Result.ok.injEq] at h
    subst h
    simp only [fromBytes, Slice.from_val, List.map_map]
    rw [show UScalar.bv ∘ UScalar.mk (ty := .U8) = id from rfl, List.map_id,
      ByteRepr.decodeAll_flatMap_encode hSize]
    simp only [dif_pos s.property, Slice.val_from]
  · simp at h

theorem toBytes_fromBytes {T : Type} [ByteRepr T] [IsScalar T] {s : Slice T}
    {bytes : Slice U8} (h : fromBytes bytes = .ok s) : toBytes s = .ok bytes := by
  unfold fromBytes at h
  split at h
  · simp at h
  · rename_i values hDecode
    split at h
    · rw [Result.ok.injEq] at h
      subst h
      simp only [toBytes, Slice.from_val, ByteRepr.flatMap_encode_of_decodeAll hDecode,
        List.map_map, show UScalar.mk (ty := .U8) ∘ UScalar.bv = id from rfl, List.map_id]
      rw [dif_pos bytes.property, Slice.val_from]
    · simp at h

@[simp]
theorem size_u8 : size (T := U8) = 1#usize := by
  change (⟨BitVec.ofNat _ 1⟩ : Usize) = 1#usize
  apply UScalar.eq_of_val_eq
  simp [UScalar.val]

@[simp]
theorem numElems_u8 (numBytes : Nat) : numElems U8 numBytes = numBytes := by
  simp [numElems]

@[simp, step_simps]
theorem toBytes_u8 (s : Slice U8) : toBytes s = .ok s := by
  simp only [toBytes, UScalar.map_mk_flatMap_encode_u8, dif_pos s.property, Slice.val_from]

@[simp, step_simps]
theorem fromBytes_u8 (s : Slice U8) : fromBytes (T := U8) s = .ok s :=
  fromBytes_toBytes (UScalar.byteRepr_size_pos _) (toBytes_u8 s)

end IsScalar

end Aeneas.Std
