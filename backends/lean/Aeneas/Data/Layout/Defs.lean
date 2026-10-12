module
public import Aeneas.Data.Byte
public import Aeneas.Data.BitVec
public import Aeneas.Data.Layout.Bytes
public import Aeneas.Data.Layout.MTypes
import all Init.Data.Nat.Power2.Basic
@[expose] public section

namespace Aeneas

/-! ## Size and Alignment -/

structure SizeAndAlign : Type 0 where
  size : Nat
  align : Nat
  wf_align : align.isPowerOfTwo
  wf_size : align ∣ size

@[grind ←]
lemma SizeAndAlign.grind_wf_align (sa : SizeAndAlign) : sa.align.isPowerOfTwo := sa.wf_align

@[grind ←]
lemma SizeAndAlign.grind_wf_size (sa : SizeAndAlign) : sa.align ∣ sa.size := sa.wf_size

namespace SizeAndAlign

lemma dvd_of_isPowerOfTwo_le {a b : Nat} (ha : a.isPowerOfTwo) (hb : b.isPowerOfTwo) (hle : a ≤ b) :
    a ∣ b := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  apply Nat.pow_dvd_pow
  rw [Nat.pow_le_pow_iff_right] at hle
  all_goals trivial

def alignUp (x A : Nat) : Nat := ((x + A - 1) / A) * A

@[simp, grind ←]
lemma le_alignUp (x : Nat) {A : Nat} (hA : 0 < A) : x ≤ alignUp x A := by
  have h := Nat.div_add_mod (x + A - 1) A
  rw [Nat.mul_comm] at h
  have := Nat.mod_lt (x + A - 1) hA
  dsimp [alignUp]
  omega

@[simp, grind ←]
lemma aligned_alignUp (x : Nat) {A : Nat} : A ∣ alignUp x A := by
  apply Nat.dvd_mul_left

lemma num_bytes_is_power_of_two {ty : IUScalarTy} : (ty.numBits / 8).isPowerOfTwo := by
  rcases ty with ⟨ty⟩ | ⟨ty⟩ <;>
    cases ty <;>
    rcases System.Platform.numBits_eq with h | h <;>
    simp [IUScalarTy.numBits, Std.IScalarTy.numBits, Std.UScalarTy.numBits, h] <;>
    decide

end SizeAndAlign

def SizeAndAlign.ValidForScalar (sa : SizeAndAlign) (ty : IUScalarTy) : Prop :=
  sa.size = ty.numBits / 8

def IUScalarTy.size (ty : IUScalarTy) : Nat := ty.numBits / 8

def IUScalarTy.reasonablyAligned (ty : IUScalarTy) : SizeAndAlign :=
  ⟨ty.size, ty.size, SizeAndAlign.num_bytes_is_power_of_two, by simp⟩

lemma IUScalarTy.reasonablyAligned_isReasonable {ty : IUScalarTy} : ty.reasonablyAligned.ValidForScalar ty := by rfl

noncomputable def IUScalarTy.size_and_align (ty : IUScalarTy) : SizeAndAlign :=
  @Classical.choose SizeAndAlign (·.ValidForScalar ty) ⟨_, ty.reasonablyAligned_isReasonable⟩

@[simp] lemma IUScalarTy.knownSize {ty : IUScalarTy} : ty.size_and_align.size = ty.size :=
  @Classical.choose_spec SizeAndAlign (·.ValidForScalar ty) ⟨_, ty.reasonablyAligned_isReasonable⟩

@[simp] lemma SizeAndAlign.sizeOneAlignOne (sa : SizeAndAlign) : sa.size = 1 → sa.align = 1 := by
  intros h
  apply Nat.le_antisymm
  · apply Nat.le_of_dvd
    { omega }
    rw [←h]
    apply sa.wf_size
  · apply Nat.pos_of_isPowerOfTwo
    apply sa.wf_align

@[simp] lemma IUScalarTy.knownAlignI8 : (IUScalarTy.signed .I8).size_and_align.align = 1 := by simp [IUScalarTy.size]

@[simp] lemma IUScalarTy.knownAlignU8 : (IUScalarTy.unsigned .U8).size_and_align.align = 1 := by simp [IUScalarTy.size]


/-! ## Core Layout Representation (`Discriminator`, `TagToWrite`, `Layout`) -/

inductive Discriminator where
  | known (n : Nat)
  | invalid
  -- the matcher is a finite total function. Almost always it will match on several ranges,
  -- and return a "default" instance for everything outside of these ranges.
  | read (offset : Nat) (ty : IUScalarTy) (matcher : BitVec ty.numBits -> Discriminator)

structure TagToWrite where
  offset : Nat
  ty : IUScalarTy
  data : IUScalar ty

-- We leverage dependent types. For now, Lean seems to be able to handle it.
inductive Layout : MType → Type 0 where
  | int : Layout (.int ty)
  | tuple
      (field_offs : Fin ts.length → Nat)
      -- NB: Lean is sensitive to the specifics of this inductive definition.
      -- For example, merging `field_layouts` and `field_offs` into one function
      -- returning a pair is not possible, as that prevents Lean from seeing that
      -- the inductive is strictly positive.
      (field_layouts : (idx : Fin ts.length) → Layout ts[idx])
      (sa : SizeAndAlign) :
      Layout (.tuple ts)
  | enum
      (variant_tags : Fin vs.length → List TagToWrite)
      (variant_layouts : (idx : Fin vs.length) → Layout vs[idx])
      (discr : Discriminator)
      (sa : SizeAndAlign) :
      Layout (.enum vs)

namespace Layout

@[reducible]
def size : {ty : MType} → Layout ty → Nat
  | .int ty, .int => ty.size
  | _, .tuple _ _ sa => sa.size
  | _, .enum _ _ _ sa => sa.size

@[simp] lemma size_int {ty} : (Layout.int : Layout (.int ty)).size = ty.size := rfl
@[simp] lemma size_tuple {ts fo fl sa} : (Layout.tuple fo fl sa : Layout (.tuple ts)).size = sa.size := rfl
@[simp] lemma size_enum {vs vt vl dc sa} : (Layout.enum vt vl dc sa : Layout (.enum vs)).size = sa.size := rfl

noncomputable def size_and_align : {ty : MType} → Layout ty → SizeAndAlign
  | .int ty, .int => ty.size_and_align
  | _, .tuple _ _ sa => sa
  | _, .enum _ _ _ sa => sa

@[simp] lemma size_known (l : Layout ty) : l.size_and_align.size = l.size :=
  by cases l <;> simp [size_and_align]

end Layout

/-! ## Little-Endian Integer Encoding and Decoding -/

namespace Endianness

@[simp] lemma mul_8_size_eq {ty : IUScalarTy} : 8 * ty.size = ty.numBits := by
  rcases ty with ⟨t⟩ | ⟨t⟩ <;> cases t <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [IUScalarTy.size, Std.IScalarTy.numBits, Std.UScalarTy.numBits, h]

def encode_bitvec {w : Nat} (sz : Nat) (bv : BitVec w) (_ : w ≤ 8 * sz := by simp only [Aeneas.Endianness.mul_8_size_eq]; omega) : Vector Byte sz :=
  Vector.ofFn λ (i : Fin sz) ↦ BitVec.extractLsb' (8 * i.val) 8 bv

lemma numBits_div_8_lt {ty : IUScalarTy} {k : Nat} (hk : k < ty.numBits) :
    k / 8 < ty.size := by
  have := mul_8_size_eq (ty := ty); omega

def decode_bitvec (ty : IUScalarTy) (bytes_data : Vector Byte ty.size) : BitVec ty.numBits :=
  BitVec.ofFn λ (k : Fin ty.numBits) ↦
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

end Endianness

/-! ## Type-Directed `encode` and `decode` of Values
    Following MiniRust's `spec/lang/representation.md`. -/

/-- Uses the `Discriminator` to decode the discriminant from the tag read out of the value's bytes.
    Returns `none` when reaching `Discriminator.invalid` and when any of the reads
    for `Discriminator.read` encounters uninitialized memory. -/
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

/-- Writes the tag described by the tagger into `bytes`. -/
def encode_discriminant {n : Nat} (bytes : Bytes n) (tagger : List TagToWrite) : Bytes n :=
  tagger.foldl (init := bytes) λ acc tag ↦
    let tag_bytes_data := Endianness.encode_bitvec tag.ty.size tag.data.bv
    acc.write_subslice_at_index tag.offset (tag_bytes_data.map .init)

namespace Layout

/-- Decode a vector of bytes into an `MVal`.
    This can fail (`none`) if `bytes` is not a valid encoding for the type,
    which typically means Undefined Behavior. -/
def decode : {ty : MType} → (l : Layout ty) → Bytes l.size → Option MVal
  -- Integers:
  | .int st, .int, bytes => do
    -- Fails if any byte is `Uninit`.
    let bytes_data ← bytes.toData
    some (.int (Endianness.decode st bytes_data))
  -- Tuples (and structs, ...):
  -- Note in particular that `decode` ignores the bytes which are before, between, or after
  -- the fields (usually called "padding").
  | .tuple ts, .tuple fo fl sa, bytes =>
    (List.finRange ts.length).mapM (λ (idx : Fin ts.length) ↦ do
      let fsz := (fl idx).size
      if h : fo idx + fsz ≤ sa.size then
        decode (fl idx) (bytes.subslice_with_length (fo idx) fsz h)
      else none)
    |>.map .tuple
  -- Enums:
  | .enum vs, .enum _ vl discriminator sa, bytes => do
    let discriminant ← decode_discriminant bytes discriminator
    if hd : discriminant < vs.length then
      let idx : Fin vs.length := ⟨discriminant, hd⟩
      let vsz := (vl idx).size
      if hsz : 0 + vsz ≤ sa.size then
        -- Decode into the variant.
        -- Because the variant is the same size as the enum we pass the full slice.
        let value ← decode (vl idx) (bytes.subslice_with_length 0 vsz hsz)
        some (.variant discriminant value)
      else none
    else none

/-- Encode `val` into a vector of bytes according to the layout `l`.
    Assumes `val` is well-formed for `ty`. -/
def encode : {ty : MType} → (l : Layout ty) → (val : MVal) → val.valid_for ty →
    Bytes l.size
  -- Integers:
  | .int st, .int, .int i, h =>
    (Endianness.encode st i (by grind)).map .init
  -- Tuples (and structs, ...):
  -- `encode` always and deterministically makes padding bytes `Uninit`.
  -- (The generic properties defined below make this the only possible choice for `encode`.)
  | .tuple ts, .tuple fo fl sa, .tuple values, hv =>
    (List.finRange ts.length).foldl (init := Bytes.uninit sa.size)
      λ (bytes : Bytes sa.size) (idx : Fin ts.length) ↦
        let i : Fin values.length := ⟨idx.val, by rw [hv.tuple_len]; exact idx.isLt⟩
        bytes.write_subslice_at_index (fo idx) (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i))
  -- Enums:
  -- Note that the discriminant may not be written into bytes that contain encoded data.
  -- This is to ensure that pointers to the data always contain valid values.
  | .enum vs, .enum vt vl _ sa, .variant discriminant data, hv =>
    -- `idx` is guaranteed to be in bounds by the well-formed check on the value.
    let idx : Fin vs.length := ⟨discriminant, hv.variant_bound⟩
    let bytes := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (vl idx) data hv.variant_proj)
    -- Write tag into the bytes around the data.
    -- This is fine as we don't allow encoded data and the tag to overlap.
    encode_discriminant bytes (vt idx)

end Layout

/-! ## Layout Validity -/

structure Layout.ScalarValidAt (st : IUScalarTy) (off : Nat) (sa : SizeAndAlign) where
  in_bounds : off + st.size ≤ sa.size

def TagToWrite.Valid (t : TagToWrite) (sa : SizeAndAlign) :=
  Layout.ScalarValidAt t.ty t.offset sa

inductive Discriminator.Valid (sa : SizeAndAlign) (n : Nat) : Discriminator → Prop where
  | known d : d < n → Discriminator.Valid _ _ (.known d)
  | invalid : Discriminator.Valid _ _ .invalid
  | read off ty matcher :
      Layout.ScalarValidAt ty off sa →
      (∀ idx, (matcher idx).Valid sa n) →
      Discriminator.Valid _ _ (.read off ty matcher)

namespace Layout

def disj_range (r1 r2 : Nat × Nat) : Prop :=
  ∀ n, r1.1 ≤ n → n < r1.2 → r2.1 ≤ n → n < r2.2 → False

structure TupleValid (field_offs : Fin n → Nat) (field_sizes : Fin n → Nat) (sa : SizeAndAlign) where
  fields_disj :
    let field_range := λ (i : Fin n) ↦ (field_offs i, field_offs i + field_sizes i)
    ∀ (i1 i2 : Fin n), i1 ≠ i2 → disj_range (field_range i1) (field_range i2)
  size_bounds : ∀ i, sa.size ≥ field_offs i + field_sizes i

structure EnumValid {vs : List MType}
      (variant_tags : Fin vs.length → List TagToWrite)
      (variant_layouts : (idx : Fin vs.length) → Layout vs[idx])
      (discr : Discriminator)
      (sa : SizeAndAlign) where
  data_sizes : ∀ idx, (variant_layouts idx).size = sa.size
  data_aligns : ∀ idx, (variant_layouts idx).size_and_align.align ≤ sa.align
  taggers_valid : ∀ idx, (variant_tags idx).Forall (·.Valid sa)
  discriminator_valid : discr.Valid sa vs.length
  /-- Writing variant `idx`'s tags into the bytes around the data does not clobber any
      initialized byte written by `variant_layouts idx`. -/
  tags_preserve_payload : ∀ (idx : Fin vs.length) (v : MVal) (hv : v.valid_for vs[idx]),
    let payload_bs := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (variant_layouts idx) v hv)
    payload_bs.le_defined (encode_discriminant payload_bs (variant_tags idx))
  /-- `decode_discriminant` recovers `idx` on any valid encoded payload + tags for variant `idx`. -/
  discr_complete : ∀ (idx : Fin vs.length) (v : MVal) (hv : v.valid_for vs[idx]),
    let payload_bs := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (variant_layouts idx) v hv)
    decode_discriminant (encode_discriminant payload_bs (variant_tags idx)) discr = some idx.val
  /-- Whenever `decode_discriminant` selects variant `idx`, all tag bytes written by `variant_tags idx`
      are less-or-equally-defined as `bytes`. -/
  discr_tags_le_defined : ∀ (bytes : Bytes sa.size) (idx : Fin vs.length),
    decode_discriminant bytes discr = some idx.val →
    (encode_discriminant (Bytes.uninit sa.size) (variant_tags idx)).le_defined bytes

inductive Valid : {ty : MType} → Layout ty → Prop where
  | int ty : Valid (.int : Layout (.int ty))
  | tuple ts fo fl sa :
      (∀ idx, (fl idx).Valid) →
      TupleValid fo (λ i ↦ (fl i).size) sa →
      Valid (.tuple fo fl sa : Layout (.tuple ts))
  | enum vs vt vl dc sa :
      (∀ idx, (vl idx).Valid) →
      EnumValid vt vl dc sa →
      Valid (.enum vt vl dc sa : Layout (.enum vs))

structure TupleReasonablyAligned (field_offs : Fin n → Nat) (field_layouts : Fin n → SizeAndAlign) (sa : SizeAndAlign) where
  fields_aligned : ∀ i, sa.align ≥ (field_layouts i).align
  offs_aligned : ∀ i, (field_layouts i).align ∣ field_offs i

inductive ReasonablyAligned : {ty : MType} → Layout ty → Prop where
  | int ty : ReasonablyAligned (.int : Layout (.int ty))
  | tuple ts fo fl sa :
      (∀ idx, (fl idx).ReasonablyAligned) →
      TupleReasonablyAligned fo (λ i ↦ (fl i).size_and_align) sa →
      ReasonablyAligned (.tuple fo fl sa : Layout (.tuple ts))
  | enum vs vt vl dc sa :
      (∀ idx, (vl idx).ReasonablyAligned) →
      (∀ idx, (vt idx).Forall (λ t ↦ t.ty.size_and_align.align ∣ t.offset)) →
      ReasonablyAligned (.enum vt vl dc sa : Layout (.enum vs))

/-! ## Generic Representation Properties (Galois Connection)
    Following MiniRust's `spec/lang/representation.md` ("Generic properties"). -/

/-- Any decoded value is well-typed for `ty`. -/
def DecodeValid {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes : Bytes l.size) (val : MVal), decode l bytes = some val → val.valid_for ty

/-- Monotonicity of `decode`:
    If `bytes1 <= bytes2`, then `l.decode(bytes1) <= l.decode(bytes2)`. -/
def DecodeMono {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes1 bytes2 : Bytes l.size),
    bytes1.le_defined bytes2 → Option.le_defined (decode l bytes1) (decode l bytes2)

/-- First round-trip property (lossless encoding):
    If `val` is well-formed for `ty`, then `l.decode(l.encode(val)) == some val`. -/
def DecodeEncode {ty : MType} (l : Layout ty) : Prop :=
  ∀ (val : MVal) (hv : val.valid_for ty), decode l (encode l val hv) = some val

/-- Second round-trip property (bytes-value-bytes resets unused/padding bytes to `Uninit`):
    If `l.decode(bytes) == some val`, then `l.encode(val) <= bytes`
    (some bytes might have become `Uninit`, but otherwise it is the same). -/
def EncodeDecodeLeDefined {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes : Bytes l.size) (val : MVal) (hv : val.valid_for ty),
    decode l bytes = some val → (encode l val hv).le_defined bytes

end Layout

end Aeneas
