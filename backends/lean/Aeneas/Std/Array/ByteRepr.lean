module
public import Aeneas.Std.Array.Array
public import Aeneas.Std.ByteRepr
@[expose] public section

/-!
# Byte representation of arrays

An array is represented by the encodings of its elements, one after the other,
and has the alignment of its elements.
-/

namespace Aeneas.Std

/-- The codec of the arrays of `n` elements: the encodings of the elements, one
after the other. -/
def Codec.array (T : Type) [ByteRepr T] (n : Usize) : Codec (Array T n) where
  size := n.val * ByteRepr.size T
  encode a := a.val.flatMap ByteRepr.encode
  decode bytes :=
    if 0 < ByteRepr.size T then
      (ByteRepr.decodeAll T bytes).bind fun values =>
        if h : values.length = n.val then some (Array.from values h) else none
    else if bytes = [] then
      if h : n.val = 0 then some (Array.from [] (by simp [h]))
      else
        (ByteRepr.decode (α := T) []).map fun x =>
          Array.from (List.replicate n.val x) (by simp)
    else none
  length_encode a := by
    rw [ByteRepr.length_flatMap_encode, a.property]
  decode_encode a := by
    split
    · rename_i hSize
      rw [ByteRepr.decodeAll_flatMap_encode hSize]
      simp [a.property]
    · rename_i hSize
      have hZero : ByteRepr.size T = 0 := by omega
      have hNil : a.val.flatMap ByteRepr.encode = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [ByteRepr.length_flatMap_encode, hZero, Nat.mul_zero]
      simp only [hNil, if_true]
      cases hVal : a.val with
      | nil =>
        have hn : n.val = 0 := by have := a.property; rw [hVal] at this; simp at this; omega
        simp only [hn, dite_true, Option.some.injEq]
        apply Array.ext; simp [Array.from_val, hVal]
      | cons x rest =>
        have hEnc : ByteRepr.encode x = [] := List.eq_nil_of_length_eq_zero (by rw [ByteRepr.length_encode, hZero])
        have hDec : ByteRepr.decode (α := T) [] = some x := by rw [← hEnc, ByteRepr.decode_encode]
        have hn : n.val ≠ 0 := by have := a.property; rw [hVal] at this; simp at this; omega
        simp only [hn, dite_false, hDec, Option.map_some, Option.some.injEq]
        apply Array.ext
        rw [Array.from_val]
        apply List.ext_getElem (by simp [a.property])
        intro i h1 h2
        simp only [List.getElem_replicate]
        exact ByteRepr.eq_of_size_zero hZero _ _
  encode_of_decode {bytes a} h := by
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨values, hValues, h⟩ := h
      split at h
      · cases h
        rw [Array.from_val]
        exact ByteRepr.flatMap_encode_of_decodeAll hValues
      · cases h
    · rename_i hSize
      have hZero : ByteRepr.size T = 0 := by omega
      split at h
      · rename_i hBytes
        subst hBytes
        apply List.eq_nil_of_length_eq_zero
        rw [ByteRepr.length_flatMap_encode, hZero, Nat.mul_zero]
      · cases h

instance Array.instByteRepr (T : Type) [ByteRepr T] (n : Usize) : ByteRepr (Array T n) :=
  ByteRepr.ofCodec (Codec.array T n) (ByteRepr.align T)
    (Nat.dvd_mul_left_of_dvd ByteRepr.align_dvd_size _)

@[simp] theorem Array.byteRepr_size (T : Type) [ByteRepr T] (n : Usize) :
    ByteRepr.size (Array T n) = n.val * ByteRepr.size T := rfl

@[simp] theorem Array.byteRepr_align (T : Type) [ByteRepr T] (n : Usize) :
    ByteRepr.align (Array T n) = ByteRepr.align T := rfl

@[simp] theorem Array.encode_eq (T : Type) [ByteRepr T] (n : Usize) (a : Array T n) :
    ByteRepr.encode a = a.val.flatMap ByteRepr.encode := rfl

end Aeneas.Std
