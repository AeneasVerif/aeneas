module
public import Aeneas.Data.Layout.Defs
@[expose] public section

namespace Aeneas

/-! ## Little-Endian Integer Encoding and Decoding -/

namespace Endianness

@[simp, grind =] lemma mul_8_size_eq {ty : IUScalarTy} : 8 * ty.size = ty.numBits := by
  rcases ty with ⟨t⟩ | ⟨t⟩ <;> cases t <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [IUScalarTy.size, Std.IScalarTy.numBits, Std.UScalarTy.numBits, h]

def encode_bitvec {w : Nat} (sz : Nat) (bv : BitVec w) (_ : w ≤ 8 * sz := by simp only [Aeneas.Endianness.mul_8_size_eq]; omega) : Vector Byte sz :=
  Vector.ofFn λ i ↦ BitVec.extractLsb' (8 * i.val) 8 bv

@[grind ←]
lemma numBits_div_8_lt {ty : IUScalarTy} {k : Nat} (hk : k < ty.numBits) :
    k / 8 < ty.size := by
  have := mul_8_size_eq (ty := ty); omega

def decode_bitvec (ty : IUScalarTy) (bytes_data : Vector Byte ty.size) : BitVec ty.numBits :=
  BitVec.ofFn λ k ↦
    (bytes_data[k.val / 8]'(numBits_div_8_lt k.isLt))[k.val % 8]'(Nat.mod_lt _ (by omega))

def encode (ty : IUScalarTy) (i : ℤ) (_ : ty.can_repr i) : Vector Byte ty.size :=
  let bv : BitVec ty.numBits := match ty with
    | .unsigned u => BitVec.ofNat u.numBits i.toNat
    | .signed s => BitVec.ofInt s.numBits i
  encode_bitvec ty.size bv

def decode (ty : IUScalarTy) (bytes_data : Vector Byte ty.size) : ℤ :=
  match ty with
  | .unsigned _ => ((decode_bitvec _ bytes_data).toNat : ℤ)
  | .signed _ => (decode_bitvec _ bytes_data).toInt

@[simp, grind =]
lemma decode_bitvec_encode_bitvec (ty : IUScalarTy) (bv : BitVec ty.numBits) :
    decode_bitvec ty (encode_bitvec ty.size bv) = bv := by
  ext k hk
  simp [decode_bitvec, encode_bitvec]
  congr 1; simp; omega

@[simp, grind =]
lemma encode_bitvec_decode_bitvec (ty : IUScalarTy) (bytes_data : Vector Byte ty.size) :
    encode_bitvec ty.size (decode_bitvec ty bytes_data) = bytes_data := by
  ext i hi r hr
  have hbit : 8 * i + r < ty.numBits := by have := mul_8_size_eq (ty := ty); omega
  simp only [encode_bitvec, Vector.getElem_ofFn, BitVec.getElem_extractLsb']
  change (decode_bitvec ty bytes_data)[8 * i + r] = bytes_data[i][r]
  simp [IUScalarTy.size, decode_bitvec, show (8 * i + r) / 8 = i by omega, show (8 * i + r) % 8 = r by omega]

@[grind ←]
lemma decode_can_repr (ty : IUScalarTy) (bytes_data : Vector Byte ty.size) :
    ty.can_repr (decode ty bytes_data) :=
  match ty with
  | .unsigned _ => ⟨⟨decode_bitvec _ bytes_data⟩, rfl⟩
  | .signed _ => ⟨⟨decode_bitvec _ bytes_data⟩, rfl⟩

@[grind =]
lemma decode_encode (ty : IUScalarTy) (i : ℤ) (h : ty.can_repr i) :
    decode ty (encode ty i h) = i := by
  obtain ⟨s, rfl⟩ := h
  cases ty with
  | unsigned u =>
    simp only [decode, encode, decode_bitvec_encode_bitvec, IUScalar.val, Std.UScalar.val,
               Int.toNat_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | signed st =>
    simp only [decode, encode, decode_bitvec_encode_bitvec, IUScalar.val, Std.IScalar.val,
               BitVec.ofInt_toInt]

@[simp, grind =]
lemma encode_decode (ty : IUScalarTy) (bytes_data : Vector Byte ty.size) :
    encode ty (decode ty bytes_data) (decode_can_repr ty bytes_data) = bytes_data := by
  cases ty with
  | unsigned u =>
    simp only [encode, decode, IUScalarTy.numBits, Int.toNat_natCast, BitVec.ofNat_toNat,
               BitVec.setWidth_eq, encode_bitvec_decode_bitvec]
  | signed st =>
    simp only [encode, decode, BitVec.ofInt_toInt, encode_bitvec_decode_bitvec]

end Endianness

/-! ## Type-Directed `encode` and `decode` of Values
    Following MiniRust's `spec/lang/representation.md`. -/

/-- Uses the `Discriminator` to decode the discriminant from the tag read out of the value's bytes.
    Returns `none` when reaching `Discriminator.invalid` and when any of the reads
    for `Discriminator.read` encounters uninitialized memory. -/
@[grind =]
def decode_discriminant {n : Nat} (bytes : Bytes n) : Discriminator → Option Nat
  | .known val => some val
  | .invalid => none
  | .read offset value_type matcher => do
      let sz := value_type.size
      if h : offset + sz ≤ n then
        let subslice := bytes.subslice_with_length offset sz h
        -- Fails if any byte is `Uninit`.
        let bytes_data ← subslice.toData
        let bv := Endianness.decode_bitvec value_type bytes_data
        decode_discriminant bytes (matcher bv)
      else none

@[simp, grind =] lemma decode_discriminant_known {n : Nat} (bytes : Bytes n) (v : Nat) :
    decode_discriminant bytes (.known v) = some v := rfl
@[simp, grind =] lemma decode_discriminant_invalid {n : Nat} (bytes : Bytes n) :
    decode_discriminant bytes .invalid = none := rfl

/-- Writes the tag described by the tagger into `bytes`. -/
def encode_discriminant {n : Nat} (bytes : Bytes n) (tagger : List TagToWrite) : Bytes n :=
  tagger.foldl (init := bytes) λ acc tag ↦
    let tag_bytes_data := Endianness.encode_bitvec tag.ty.size tag.data.bv
    acc.write_subslice_at_index tag.offset (tag_bytes_data.map .init)

@[grind ←]
lemma decode_discriminant_mono {n : Nat} {bs1 bs2 : Bytes n} (h_le : bs1.le_defined bs2) :
    ∀ d : Discriminator, Option.le_defined (decode_discriminant bs1 d) (decode_discriminant bs2 d)
  | .known _ => rfl
  | .invalid => trivial
  | .read offset value_type matcher => by
    unfold decode_discriminant; dsimp only
    split
    case isFalse => trivial
    case isTrue h =>
      dsimp only [Option.bind_eq_bind]
      cases h_data : (bs1.subslice_with_length offset value_type.size h).toData with
      | none => simp
      | some bytes_data =>
        have h_sub_eq := Bytes.eq_of_toData_some_le_defined h_data (Bytes.subslice_le_defined h_le _ _ h)
        rw [← h_sub_eq, h_data]
        exact decode_discriminant_mono h_le _

@[grind ←]
lemma encode_discriminant_le_defined {n : Nat} (payload bytes : Bytes n) (tags : List TagToWrite)
    (h_pay : payload.le_defined bytes)
    (h_tag : (encode_discriminant (Bytes.uninit n) tags).le_defined bytes) :
    (encode_discriminant payload tags).le_defined bytes :=
  Bytes.foldl_write_subslice_overlay_le_defined tags (·.offset)
    (λ tag ↦ (Endianness.encode_bitvec tag.ty.size tag.data.bv).map .init)
    payload bytes h_pay h_tag

namespace Layout

/-- Decode a vector of bytes into an `MVal`.
    This can fail (`none`) if `bytes` is not a valid encoding for the type,
    which typically means Undefined Behavior. -/
def decode : {ty : MType} → (l : Layout ty) → Bytes l.size → Option MVal
  -- Integers:
  | .int st, .int sa h, bytes => do
    -- Fails if any byte is `Uninit`.
    let bytes : Bytes sa.size := bytes
    let bytes_data ← (h.size_eq ▸ bytes).toData
    some (.int (Endianness.decode st bytes_data))
  -- Tuples (and structs, ...):
  -- Note in particular that `decode` ignores the bytes which are before, between, or after
  -- the fields (usually called "padding").
  | .tuple ts _, .tuple fo fl sa, bytes =>
    (List.range ts.length).attach.mapM (λ (x : Subtype _) ↦ do
      let fsz := (fl x.val (by grind)).size
      if h : fo x.val (by grind) + fsz ≤ sa.size then
        decode (fl x.val (by grind)) (bytes.subslice_with_length (fo x.val (by grind)) fsz h)
      else none)
    |>.map .tuple
  -- Enums:
  | .enum vs _, .enum _ vl discriminator sa, bytes => do
    let discriminant ← decode_discriminant bytes discriminator
    if hd : discriminant < vs.length then
      let vsz := (vl discriminant hd).size
      if hsz : 0 + vsz ≤ sa.size then
        -- Decode into the variant.
        -- Because the variant is the same size as the enum we pass the full slice.
        let value ← decode (vl discriminant hd) (bytes.subslice_with_length 0 vsz hsz)
        some (.variant discriminant value)
      else none
    else none

/-- Encode `val` into a vector of bytes according to the layout `l`.
    Assumes `val` is well-formed for `ty`. -/
def encode : {ty : MType} → (l : Layout ty) → (val : MVal) → val.valid_for ty →
    Bytes l.size
  -- Integers:
  | .int st, .int _ hs, .int i, h =>
    (hs.size_eq ▸  Endianness.encode st i (by grind)).map .init
  -- Tuples (and structs, ...):
  -- `encode` always and deterministically makes padding bytes `Uninit`.
  -- (The generic properties defined below make this the only possible choice for `encode`.)
  | .tuple ts _, .tuple fo fl sa, .tuple values, hv =>
    (List.range ts.length).attach.foldl (init := Bytes.uninit sa.size)
      λ (bytes : Bytes sa.size) x ↦
        bytes.write_subslice_at_index (fo x.val (by grind))
          (encode (fl x.val (by grind)) (values[x.val]'(by grind)) (by grind))
  -- Enums:
  -- Note that the discriminant may not be written into bytes that contain encoded data.
  -- This is to ensure that pointers to the data always contain valid values.
  | .enum vs _, .enum vt vl _ sa, .variant discriminant data, hv =>
    let bytes := (Bytes.uninit sa.size).write_subslice_at_index 0
      (encode (vl discriminant hv.variant_bound) data hv.variant_proj)
    -- Write tag into the bytes around the data.
    -- This is fine as we don't allow encoded data and the tag to overlap.
    encode_discriminant bytes (vt discriminant hv.variant_bound)

/-! ## Generic Representation Properties (Galois Connection)
    Following MiniRust's `spec/lang/representation.md` ("Generic properties").
    Proven in `GaloisConnection.lean` -/

/-- Any decoded value is well-typed for `ty`. -/
@[grind =]
def DecodeValid {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes : Bytes l.size) (val : MVal), decode l bytes = some val → val.valid_for ty

/-- Monotonicity of `decode`:
    If `bytes1 <= bytes2`, then `l.decode(bytes1) <= l.decode(bytes2)`. -/
@[grind =]
def DecodeMono {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes1 bytes2 : Bytes l.size),
    bytes1.le_defined bytes2 → Option.le_defined (decode l bytes1) (decode l bytes2)

/-- First round-trip property (lossless encoding):
    If `val` is well-formed for `ty`, then `l.decode(l.encode(val)) == some val`. -/
@[grind =]
def DecodeEncode {ty : MType} (l : Layout ty) : Prop :=
  ∀ (val : MVal) (hv : val.valid_for ty), decode l (encode l val hv) = some val

/-- Second round-trip property (bytes-value-bytes resets unused/padding bytes to `Uninit`):
    If `l.decode(bytes) == some val`, then `l.encode(val) <= bytes`
    (some bytes might have become `Uninit`, but otherwise it is the same). -/
@[grind =]
def EncodeDecodeLeDefined {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes : Bytes l.size) (val : MVal) (hv : val.valid_for ty),
    decode l bytes = some val → (encode l val hv).le_defined bytes

end Layout

end Aeneas
