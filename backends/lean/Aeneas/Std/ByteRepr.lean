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

/-- A fixed-size encoding of the values of `α` as bytes: a `ByteRepr` without the
alignment.  Codecs compose, which is how the byte representations of arrays and
structs are built. -/
structure Codec (α : Type) where
  size : Nat
  encode : α → List Byte
  decode : List Byte → Option α
  length_encode (x : α) : (encode x).length = size
  decode_encode (x : α) : decode (encode x) = some x
  encode_of_decode {bytes : List Byte} {x : α} :
    decode bytes = some x → encode x = bytes

namespace Codec

/-- The codec of a type with a byte representation. -/
def ofByteRepr (α : Type) [ByteRepr α] : Codec α where
  size := ByteRepr.size α
  encode := ByteRepr.encode
  decode := ByteRepr.decode
  length_encode := ByteRepr.length_encode
  decode_encode := ByteRepr.decode_encode
  encode_of_decode := ByteRepr.encode_of_decode

/-- `n` padding bytes, which are zero. -/
def pad (n : Nat) : Codec Unit where
  size := n
  encode _ := List.replicate n 0
  decode bytes := if bytes = List.replicate n 0 then some () else none
  length_encode _ := by simp
  decode_encode _ := by simp
  encode_of_decode {bytes x} h := by
    split at h
    · simp_all
    · cases h

/-- The concatenation of two codecs. -/
def prod (ca : Codec α) (cb : Codec β) : Codec (α × β) where
  size := ca.size + cb.size
  encode p := ca.encode p.1 ++ cb.encode p.2
  decode bytes := do
    let a ← ca.decode (bytes.take ca.size)
    let b ← cb.decode (bytes.drop ca.size)
    pure (a, b)
  length_encode p := by simp [ca.length_encode, cb.length_encode]
  decode_encode p := by
    have h := ca.length_encode p.1
    simp [List.take_left' h, List.drop_left' h, ca.decode_encode, cb.decode_encode]
  encode_of_decode {bytes x} h := by
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [ca.encode_of_decode ha, cb.encode_of_decode hb]

/-- Transport a codec along a bijection. -/
def map (c : Codec β) (f : α → β) (g : β → α)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) : Codec α where
  size := c.size
  encode a := c.encode (f a)
  decode bytes := (c.decode bytes).map g
  length_encode a := c.length_encode (f a)
  decode_encode a := by simp [c.decode_encode, hgf]
  encode_of_decode {bytes x} h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    rw [hfg]; exact c.encode_of_decode hb

end Codec

/-- A byte representation from a codec and an alignment. -/
@[reducible] def ByteRepr.ofCodec (c : Codec α) (align : Nat) (h : align ∣ c.size) : ByteRepr α where
  size := c.size
  align := align
  align_dvd_size := h
  encode := c.encode
  decode := c.decode
  length_encode := c.length_encode
  decode_encode := c.decode_encode
  encode_of_decode := c.encode_of_decode


/-- In a type with a zero-sized byte representation, all values are equal. -/
theorem ByteRepr.eq_of_size_zero [ByteRepr T] (h : ByteRepr.size T = 0) (x y : T) : x = y := by
  have hx : ByteRepr.encode x = [] :=
    List.eq_nil_of_length_eq_zero (by rw [ByteRepr.length_encode, h])
  have hy : ByteRepr.encode y = [] :=
    List.eq_nil_of_length_eq_zero (by rw [ByteRepr.length_encode, h])
  have := ByteRepr.decode_encode x
  rw [hx, ← hy, ByteRepr.decode_encode] at this
  exact (Option.some.inj this).symm

end Aeneas.Std
