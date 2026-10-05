module
public import Aeneas.Data.Byte
@[expose] public section

namespace Aeneas.Std

/-- A fixed-size encoding of the values of `α` as bytes: what lets a value of `α`
live in the heap.  Decoding accepts exactly the encodings, so the bytes found
at an address determine the value they hold.  A value of `α` may only be read
or written at an address that is a multiple of `align`, which divides `size` as
in Rust. -/
class ByteRepr (α : Type) where
  size : Nat
  align : Nat
  align_dvd_size : align ∣ size
  encode : α → List Byte
  decode : List Byte → Option α
  length_encode (x : α) : (encode x).length = size
  decode_encode (x : α) : decode (encode x) = some x
  encode_of_decode {bytes : List Byte} {x : α} :
    decode bytes = some x → encode x = bytes

namespace ByteRepr

theorem length_flatMap_encode {T : Type} [ByteRepr T] (values : List T) :
    (values.flatMap encode).length = values.length * size T := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.flatMap_cons, List.length_append, length_encode, ih,
        List.length_cons, Nat.succ_mul]
      omega

def decodeAll (T : Type) [ByteRepr T] (bytes : List Byte) : Option (List T) :=
  match bytes with
  | [] => some []
  | b :: bs =>
    if hSize : 0 < size T then do
      let value ← decode ((b :: bs).take (size T))
      let rest ← decodeAll T ((b :: bs).drop (size T))
      pure (value :: rest)
    else none
termination_by bytes.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem decodeAll_flatMap_encode {T : Type} [ByteRepr T] (hSize : 0 < size T)
    (values : List T) : decodeAll T (values.flatMap encode) = some values := by
  induction values with
  | nil => rw [List.flatMap_nil, decodeAll]
  | cons value rest ih =>
    have hLength := length_encode value
    obtain ⟨b, bs, hCons⟩ : ∃ b bs, (value :: rest).flatMap encode = b :: bs := by
      cases hBytes : (value :: rest).flatMap encode with
      | nil =>
        have := congrArg List.length hBytes
        simp only [List.flatMap_cons, List.length_append, List.length_nil] at this
        omega
      | cons b bs => exact ⟨b, bs, rfl⟩
    rw [hCons, decodeAll, dif_pos hSize, ← hCons, List.flatMap_cons,
      List.take_left' hLength, List.drop_left' hLength, decode_encode, ih]
    rfl

theorem flatMap_encode_of_decodeAll {T : Type} [ByteRepr T] {bytes : List Byte}
    {values : List T} (h : decodeAll T bytes = some values) :
    values.flatMap encode = bytes := by
  fun_induction decodeAll T bytes generalizing values with
  | case1 => cases h; rfl
  | case2 b bs hSize ih =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨value, hValue, rest, hRest, rfl⟩ := h
    rw [List.flatMap_cons, encode_of_decode hValue, ih hRest, List.take_append_drop]
  | case3 => cases h

end ByteRepr

end Aeneas.Std
