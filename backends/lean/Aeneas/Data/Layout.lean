module
public import Aeneas.Data.Byte
public import Aeneas.Data.BitVec
public import Aeneas.Data.MTypes
import all Init.Data.Nat.Power2.Basic
public section

namespace Aeneas

/-! ## Size and Alignment -/

structure SizeAndAlign : Type 0 where
  size : Nat
  align : Nat
  wf_align : align.isPowerOfTwo
  wf_size : align ∣ size

namespace SizeAndAlign

lemma dvd_of_isPowerOfTwo_le {a b : Nat} (ha : a.isPowerOfTwo) (hb : b.isPowerOfTwo) (hle : a ≤ b) :
    a ∣ b := by
  obtain ⟨ka, rfl⟩ := ha; obtain ⟨kb, rfl⟩ := hb
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle)

def alignUp (x A : Nat) : Nat := ((x + A - 1) / A) * A

lemma le_alignUp (x : Nat) {A : Nat} (hA : 0 < A) : x ≤ alignUp x A := by
  have h := Nat.div_add_mod (x + A - 1) A
  rw [Nat.mul_comm] at h; have := Nat.mod_lt (x + A - 1) hA; dsimp [alignUp]; omega

lemma num_bytes_is_power_of_two {ty : IUScalarTy} : (ty.numBits / 8).isPowerOfTwo := by
  rcases ty with ⟨ty⟩ | ⟨ty⟩ <;> cases ty <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [IUScalarTy.numBits, Std.IScalarTy.numBits, Std.UScalarTy.numBits, h] <;> decide

end SizeAndAlign

def IUScalarTy.size_and_align (ty : IUScalarTy) : SizeAndAlign :=
  ⟨ty.numBits / 8, ty.numBits / 8, SizeAndAlign.num_bytes_is_power_of_two, by simp⟩

/-! ## Core Layout Representation (`Discriminator`, `TagToWrite`, `Layout`) -/

inductive Discriminator where
  | known (n : Nat)
  | invalid
  -- the matcher is a finite total function
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

@[expose, simp]
def size_and_align : {ty : MType} → Layout ty → SizeAndAlign
  | .int ty, .int => ty.size_and_align
  | _, .tuple _ _ sa => sa
  | _, .enum _ _ _ sa => sa

end Layout

/-! ## Abstract Bytes and Definedness Relation (`le_defined`)
    Following MiniRust's `spec/lang/representation.md`. -/

inductive AbstractByte where
  | uninit
  | init (data : Byte)
deriving DecidableEq

namespace AbstractByte

@[simp]
def data : AbstractByte → Option Byte
  | .uninit => none
  | .init b => some b

/-- Returns whether `self` is less or as defined as `other` (`b1 <= b2`). -/
def le_defined (self other : AbstractByte) : Prop :=
  match self, other with
  -- `Uninit <= _`: initializing something makes it "more defined".
  | .uninit, _ => True
  -- Among initialized bytes (without provenance), data must be equal.
  | .init data1, .init data2 => data1 = data2
  -- Nothing else is related.
  | _, _ => False

@[simp] lemma le_defined_uninit (b : AbstractByte) : AbstractByte.uninit.le_defined b := trivial
@[simp] lemma le_defined_refl (b : AbstractByte) : b.le_defined b := by cases b <;> simp [le_defined]

end AbstractByte

abbrev Bytes (n : Nat) := Vector AbstractByte n

namespace Bytes

def uninit (n : Nat) : Bytes n := Vector.replicate n .uninit

/-- The order on `Bytes` is bytewise `le_defined`. -/
def le_defined {n : Nat} (self other : Bytes n) : Prop :=
  ∀ i : Fin n, (self[i]).le_defined (other[i])

@[simp] lemma le_defined_refl {n : Nat} (bs : Bytes n) : bs.le_defined bs :=
  λ i ↦ AbstractByte.le_defined_refl bs[i]

@[simp] lemma uninit_getElem (n : Nat) (j : Fin n) : (Bytes.uninit n)[j] = .uninit := by simp [uninit]

def subslice_with_length {n : Nat} (bytes : Bytes n) (offset length : Nat) (h : offset + length ≤ n) : Bytes length :=
  Vector.ofFn λ (i : Fin length) ↦ bytes[offset + i.val]'(by omega)

def write_subslice_at_index {n m : Nat} (bytes : Bytes n) (offset : Nat) (subslice : Bytes m) : Bytes n :=
  Vector.ofFn λ (j : Fin n) ↦
    if h : offset ≤ j.val ∧ j.val < offset + m then subslice[j.val - offset]'(by omega) else bytes[j]

lemma write_subslice_at_index_lt {n m : Nat} (bs : Bytes n) (off : Nat) (sub : Bytes m) {j : Fin n} (hlt : j.val < off) :
    (bs.write_subslice_at_index off sub)[j] = bs[j] := by simp [write_subslice_at_index]; omega

lemma write_subslice_at_index_zero_lt {n m : Nat} (bs : Bytes n) (sub : Bytes m) {j : Fin n} (hlt : j.val < m) :
    (bs.write_subslice_at_index 0 sub)[j] = sub[j.val] := by simp [write_subslice_at_index, hlt]

lemma write_subslice_at_index_zero_ge {n m : Nat} (bs : Bytes n) (sub : Bytes m) {j : Fin n} (hge : m ≤ j.val) :
    (bs.write_subslice_at_index 0 sub)[j] = bs[j] := by simp [write_subslice_at_index]; omega

@[simp]
lemma subslice_write_subslice_zero {n m : Nat} (bs : Bytes n) (sub : Bytes m) (h : 0 + m ≤ n) :
    (bs.write_subslice_at_index 0 sub).subslice_with_length 0 m h = sub := by
  ext i hi; simp [subslice_with_length, write_subslice_at_index]

lemma subslice_write_subslice_self {n m : Nat} (bs : Bytes n) (off : Nat) (sub : Bytes m) (h : off + m ≤ n) :
    (bs.write_subslice_at_index off sub).subslice_with_length off m h = sub := by
  ext i hi; simp [subslice_with_length, write_subslice_at_index]

lemma subslice_le_defined {n : Nat} {bs1 bs2 : Bytes n} (h_le : bs1.le_defined bs2)
    (off len : Nat) (h : off + len ≤ n) :
    (bs1.subslice_with_length off len h).le_defined (bs2.subslice_with_length off len h) :=
  λ i ↦ by simpa [subslice_with_length] using h_le ⟨off + i.val, by omega⟩

def toData {n : Nat} (bytes : Bytes n) : Option (Vector Byte n) :=
  if h : ∀ i : Fin n, (bytes[i]).data.isSome then some (Vector.ofFn λ i ↦ (bytes[i]).data.get (h i)) else none

@[simp]
lemma toData_map_init {n : Nat} (v : Vector Byte n) : Bytes.toData (v.map AbstractByte.init) = some v := by
  unfold toData; rw [dif_pos (by intro i; simp)]; congr 1; ext i hi; simp

lemma getElem_of_toData {n : Nat} {bs : Bytes n} {v : Vector Byte n}
    (h : bs.toData = some v) (i : Nat) (hi : i < n) : bs[i] = .init v[i] := by
  have eq_init_get : ∀ {b : AbstractByte} (hb : b.data.isSome), b = .init (b.data.get hb)
    | .uninit, hb => by simp at hb
    | .init _, _ => rfl
  unfold toData at h; split at h <;> [injection h with h; cases h]
  subst h; simp only [Vector.getElem_ofFn]; exact eq_init_get _

lemma eq_of_toData_some_le_defined {n : Nat} {bs1 bs2 : Bytes n} {v : Vector Byte n}
    (h_data : bs1.toData = some v) (h_le : bs1.le_defined bs2) : bs1 = bs2 := by
  ext i hi
  have h1 : bs1[i] = .init v[i] := getElem_of_toData h_data i hi
  have hle : bs1[i].le_defined bs2[i] := h_le ⟨i, hi⟩
  rw [h1] at hle ⊢
  cases hb2 : bs2[i] with
  | uninit => rw [hb2] at hle; cases hle
  | init b2 => rw [hb2] at hle; simp [AbstractByte.le_defined] at hle; subst hle; rfl

end Bytes

/-- On `Option`, `none <= _`, and `some v1 <= some v2` iff `v1 = v2`. -/
def Option.le_defined {α : Type u} (self other : Option α) : Prop :=
  match self, other with
  | none, _ => True
  | some l, some r => l = r
  | _, _ => False

namespace Option.le_defined

@[simp] lemma refl {α : Type u} (o : Option α) : Option.le_defined o o := by
  cases o <;> simp [Option.le_defined]

lemma eq_of_some {α : Type u} {a : α} {o : Option α} (h : Option.le_defined (some a) o) : o = some a := by
  cases o <;> simp [Option.le_defined] at h; congr 1; exact h.symm

lemma map {α β : Type u} {o1 o2 : Option α} (f : α → β) (h : Option.le_defined o1 o2) :
    Option.le_defined (o1.map f) (o2.map f) := by
  cases o1 with
  | none => trivial
  | some a => rw [eq_of_some h]; simp

lemma bind {α β : Type u} {o1 o2 : Option α} {f1 f2 : α → Option β}
    (ho : Option.le_defined o1 o2) (hf : ∀ a, o1 = some a → Option.le_defined (f1 a) (f2 a)) :
    Option.le_defined (o1 >>= f1) (o2 >>= f2) := by
  cases o1 with
  | none => trivial
  | some a => rw [eq_of_some ho]; exact hf a rfl

end Option.le_defined

/-! ## Little-Endian Integer Encoding and Decoding -/

namespace Endianness

def encode_bitvec {w : Nat} (sz : Nat) (bv : BitVec w) : Vector Byte sz :=
  Vector.ofFn λ (i : Fin sz) ↦ BitVec.extractLsb' (8 * i.val) 8 bv

lemma mul_8_size_eq {ty : IUScalarTy} : 8 * ty.size_and_align.size = ty.numBits := by
  rcases ty with ⟨t⟩ | ⟨t⟩ <;> cases t <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [IUScalarTy.size_and_align, IUScalarTy.numBits, Std.IScalarTy.numBits, Std.UScalarTy.numBits, h]

lemma numBits_div_8_lt {ty : IUScalarTy} {k : Nat} (hk : k < ty.numBits) :
    k / 8 < ty.size_and_align.size := by
  have := mul_8_size_eq (ty := ty); omega

def decode_bitvec (ty : IUScalarTy) (bytes_data : Vector Byte ty.size_and_align.size) : BitVec ty.numBits :=
  BitVec.ofFn λ (k : Fin ty.numBits) ↦
    (bytes_data[k.val / 8]'(numBits_div_8_lt k.isLt))[k.val % 8]'(Nat.mod_lt _ (by omega))

@[simp]
lemma decode_bitvec_encode_bitvec (ty : IUScalarTy) (bv : BitVec ty.numBits) :
    decode_bitvec ty (encode_bitvec ty.size_and_align.size bv) = bv := by
  apply BitVec.ext; intro k hk
  simp only [decode_bitvec, BitVec.getElem_ofFn, encode_bitvec, Vector.getElem_ofFn, BitVec.getElem_extractLsb']
  change bv.getLsbD (8 * (k / 8) + k % 8) = bv.getLsbD k
  congr 1; omega

lemma encode_bitvec_decode_bitvec (ty : IUScalarTy) (bytes_data : Vector Byte ty.size_and_align.size) :
    encode_bitvec ty.size_and_align.size (decode_bitvec ty bytes_data) = bytes_data := by
  ext i hi r hr
  have hbit : 8 * i + r < ty.numBits := by have := mul_8_size_eq (ty := ty); omega
  simp only [encode_bitvec, Vector.getElem_ofFn, BitVec.getElem_extractLsb']
  change (decode_bitvec ty bytes_data)[8 * i + r] = bytes_data[i][r]
  simp [decode_bitvec, show (8 * i + r) / 8 = i by omega, show (8 * i + r) % 8 = r by omega]

def encode (ty : IUScalarTy) (i : ℤ) : Vector Byte ty.size_and_align.size :=
  let bv : BitVec ty.numBits := match ty with
    | .unsigned u => BitVec.ofNat u.numBits i.toNat
    | .signed s => BitVec.ofInt s.numBits i
  encode_bitvec ty.size_and_align.size bv

def decode (ty : IUScalarTy) (bytes_data : Vector Byte ty.size_and_align.size) : ℤ :=
  match ty with
  | .unsigned _ => ((decode_bitvec _ bytes_data).toNat : ℤ)
  | .signed _ => (decode_bitvec _ bytes_data).toInt

lemma decode_can_repr (ty : IUScalarTy) (bytes_data : Vector Byte ty.size_and_align.size) :
    ty.can_repr (decode ty bytes_data) :=
  match ty with
  | .unsigned _ => ⟨⟨decode_bitvec _ bytes_data⟩, rfl⟩
  | .signed _ => ⟨⟨decode_bitvec _ bytes_data⟩, rfl⟩

lemma decode_encode (ty : IUScalarTy) (i : ℤ) (h : ty.can_repr i) :
    decode ty (encode ty i) = i := by
  obtain ⟨s, rfl⟩ := h
  cases ty with
  | unsigned u =>
    simp only [decode, encode, decode_bitvec_encode_bitvec, IUScalar.val, Std.UScalar.val,
               Int.toNat_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | signed st =>
    simp only [decode, encode, decode_bitvec_encode_bitvec, IUScalar.val, Std.IScalar.val,
               BitVec.ofInt_toInt]

lemma encode_decode (ty : IUScalarTy) (bytes_data : Vector Byte ty.size_and_align.size) :
    encode ty (decode ty bytes_data) = bytes_data := by
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
def decode_discriminant {n : Nat} (bytes : Bytes n) : Discriminator → Option Nat
  | .known val => some val
  | .invalid => none
  | .read offset value_type matcher => do
      let sz := value_type.size_and_align.size
      if h : offset + sz ≤ n then
        let subslice := bytes.subslice_with_length offset sz h
        -- Fails if any byte is `Uninit`.
        let bytes_data ← subslice.toData
        let bv := Endianness.decode_bitvec value_type bytes_data
        decode_discriminant bytes (matcher bv)
      else none

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
      cases h_data : (bs1.subslice_with_length offset value_type.size_and_align.size h).toData with
      | none => simp [Option.le_defined]
      | some bytes_data =>
        have h_sub_eq := Bytes.eq_of_toData_some_le_defined h_data (Bytes.subslice_le_defined h_le offset _ h)
        rw [← h_sub_eq, h_data]
        exact decode_discriminant_mono h_le (matcher (Endianness.decode_bitvec value_type bytes_data))

/-- Writes the tag described by the tagger into `bytes`. -/
def encode_discriminant {n : Nat} (bytes : Bytes n) (tagger : List TagToWrite) : Bytes n :=
  tagger.foldl (init := bytes) λ acc tag ↦
    let tag_bytes_data := Endianness.encode_bitvec tag.ty.size_and_align.size tag.data.bv
    acc.write_subslice_at_index tag.offset (tag_bytes_data.map .init)

lemma encode_discriminant_dichotomy {n : Nat} (tags : List TagToWrite) (j : Fin n) :
    (∀ b : Bytes n, (encode_discriminant b tags)[j] = b[j]) ∨
    (∀ b1 b2 : Bytes n, (encode_discriminant b1 tags)[j] = (encode_discriminant b2 tags)[j]) := by
  induction tags with
  | nil => exact .inl (λ _ ↦ rfl)
  | cons t ts ih =>
    rcases ih with h_id | h_const
    · by_cases hj : t.offset ≤ j.val ∧ j.val < t.offset + t.ty.size_and_align.size
      · right; intro b1 b2
        change (encode_discriminant _ ts)[j] = (encode_discriminant _ ts)[j]
        rw [h_id, h_id]; simp [Bytes.write_subslice_at_index, hj]
      · left; intro b
        change (encode_discriminant _ ts)[j] = b[j]
        rw [h_id]; simp [Bytes.write_subslice_at_index, hj]
    · right; intro b1 b2
      exact h_const _ _

lemma encode_discriminant_le_defined {n : Nat} (payload bytes : Bytes n) (tags : List TagToWrite)
    (h_pay : payload.le_defined bytes)
    (h_tag : (encode_discriminant (Bytes.uninit n) tags).le_defined bytes) :
    (encode_discriminant payload tags).le_defined bytes := λ j ↦ by
  rcases encode_discriminant_dichotomy tags j with h | h
  · rw [h payload]; exact h_pay j
  · rw [h payload (Bytes.uninit n)]; exact h_tag j

namespace Layout

/-- Decode a vector of bytes into an `MVal`.
    This can fail (`none`) if `bytes` is not a valid encoding for the type,
    which typically means Undefined Behavior. -/
def decode : {ty : MType} → (l : Layout ty) → Bytes l.size_and_align.size → Option MVal
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
      let fsz := (fl idx).size_and_align.size
      if h : fo idx + fsz ≤ sa.size then
        decode (fl idx) (bytes.subslice_with_length (fo idx) fsz h)
      else none)
    |>.map .tuple
  -- Enums:
  | .enum vs, .enum _ vl discriminator sa, bytes => do
    let discriminant ← decode_discriminant bytes discriminator
    if hd : discriminant < vs.length then
      let idx : Fin vs.length := ⟨discriminant, hd⟩
      let vsz := (vl idx).size_and_align.size
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
    Bytes l.size_and_align.size
  -- Integers:
  | .int st, .int, .int i, _ =>
    (Endianness.encode st i).map .init
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
  in_bounds : off + st.size_and_align.size ≤ sa.size
  aligned : st.size_and_align.align ∣ off

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

structure TupleValid (field_offs : Fin n → Nat) (field_layouts : Fin n → SizeAndAlign) (sa : SizeAndAlign) where
  fields_disj :
    let field_range := λ (i : Fin n) ↦ (field_offs i, field_offs i + (field_layouts i).size)
    ∀ (i1 i2 : Fin n), i1 ≠ i2 → disj_range (field_range i1) (field_range i2)
  fields_aligned : ∀ i, sa.align ≥ (field_layouts i).2
  size_bounds : ∀ i, sa.size ≥ field_offs i + (field_layouts i).1
  offs_aligned : ∀ i, (field_layouts i).2 ∣ field_offs i

structure EnumValid {vs : List MType}
      (variant_tags : Fin vs.length → List TagToWrite)
      (variant_layouts : (idx : Fin vs.length) → Layout vs[idx])
      (discr : Discriminator)
      (sa : SizeAndAlign) where
  data_sizes : ∀ idx, (variant_layouts idx).size_and_align.size = sa.size
  data_aligns : ∀ idx, (variant_layouts idx).size_and_align.align ≤ sa.align
  taggers_valid : discr.Valid sa vs.length
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
      TupleValid fo (λ i ↦ (fl i).size_and_align) sa →
      Valid (.tuple fo fl sa : Layout (.tuple ts))
  | enum vs vt vl dc sa :
      (∀ idx, (vl idx).Valid) →
      EnumValid vt vl dc sa →
      Valid (.enum vt vl dc sa : Layout (.enum vs))

/-! ## Generic Representation Properties (Galois Connection)
    Following MiniRust's `spec/lang/representation.md` ("Generic properties"). -/

/-- Any decoded value is well-typed for `ty`. -/
def DecodeValid {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes : Bytes l.size_and_align.size) (val : MVal), decode l bytes = some val → val.valid_for ty

/-- Monotonicity of `decode`:
    If `bytes1 <= bytes2`, then `l.decode(bytes1) <= l.decode(bytes2)`. -/
def DecodeMono {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes1 bytes2 : Bytes l.size_and_align.size),
    bytes1.le_defined bytes2 → Option.le_defined (decode l bytes1) (decode l bytes2)

/-- First round-trip property (lossless encoding):
    If `val` is well-formed for `ty`, then `l.decode(l.encode(val)) == some val`. -/
def DecodeEncode {ty : MType} (l : Layout ty) : Prop :=
  ∀ (val : MVal) (hv : val.valid_for ty), decode l (encode l val hv) = some val

/-- Second round-trip property (bytes-value-bytes resets unused/padding bytes to `Uninit`):
    If `l.decode(bytes) == some val`, then `l.encode(val) <= bytes`
    (some bytes might have become `Uninit`, but otherwise it is the same). -/
def EncodeDecodeLeDefined {ty : MType} (l : Layout ty) : Prop :=
  ∀ (bytes : Bytes l.size_and_align.size) (val : MVal) (hv : val.valid_for ty),
    decode l bytes = some val → (encode l val hv).le_defined bytes

/-! ### Helper Lemmas for Proving the Galois Connection Properties -/

private lemma list_mapM_mono {α β : Type} {f1 f2 : α → Option β} (xs : List α)
    (hf : ∀ x ∈ xs, Option.le_defined (f1 x) (f2 x)) :
    Option.le_defined (xs.mapM f1) (xs.mapM f2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons]
    refine Option.le_defined.bind (hf x List.mem_cons_self) λ _ _ ↦ ?_
    exact Option.le_defined.bind (ih λ a ha ↦ hf a (List.mem_cons_of_mem x ha)) λ _ _ ↦ rfl

private lemma list_mapM_eq_some_length {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], _, h => by simp at h; subst h; rfl
  | x :: xs, _, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, _, zs, hzs, rfl⟩ := h
    simp [list_mapM_eq_some_length hzs]

private lemma list_mapM_eq_some_getElem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β} (h : xs.mapM f = some ys) (i : Nat) (hi : i < xs.length),
      f xs[i] = some (ys[i]'(by rw [list_mapM_eq_some_length h]; exact hi))
  | x :: xs, _, h, 0, _ => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, zs, _, rfl⟩ := h; exact hy
  | x :: xs, _, h, i + 1, hi => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, _, zs, hzs, rfl⟩ := h
    exact list_mapM_eq_some_getElem hzs i (Nat.lt_of_succ_lt_succ hi)

private lemma list_mapM_eq_some_of_getElem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β} (h_len : ys.length = xs.length),
      (∀ (i : Nat) (hi : i < xs.length), f xs[i] = some (ys[i]'(by rw [h_len]; exact hi))) →
      xs.mapM f = some ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, h_len, h_get => by
    simp only [List.mapM_cons, Option.bind_eq_bind]
    have h0 : f x = some y := h_get 0 (Nat.zero_lt_succ _)
    rw [h0]; simp only [Option.bind_some]
    rw [list_mapM_eq_some_of_getElem (Nat.succ.inj h_len)
          (λ i hi ↦ h_get (i + 1) (Nat.succ_lt_succ hi))]
    rfl

private lemma list_mapM_finRange_eq_some {α : Type} {n : Nat} {f : Fin n → Option α} {ys : List α}
    (h : (List.finRange n).mapM f = some ys) (idx : Fin n) :
    f idx = some (ys[idx.val]'(by rw [list_mapM_eq_some_length h, List.length_finRange]; exact idx.isLt)) := by
  have := list_mapM_eq_some_getElem h idx.val (by rw [List.length_finRange]; exact idx.isLt)
  convert this using 2; ext; simp

private lemma list_mapM_finRange_of_getElem {α : Type} {n : Nat} {f : Fin n → Option α} {ys : List α}
    (h_len : ys.length = n)
    (h_get : ∀ (idx : Fin n), f idx = some (ys[idx.val]'(by rw [h_len]; exact idx.isLt))) :
    (List.finRange n).mapM f = some ys := by
  apply list_mapM_eq_some_of_getElem (by rw [List.length_finRange]; exact h_len)
  intro i hi
  convert h_get ⟨i, by rw [List.length_finRange] at hi; exact hi⟩ using 2
  ext; simp

private lemma subslice_write_subslice_disj {n m1 m2 : Nat} (bs : Bytes n) (off1 off2 : Nat)
    (sub2 : Bytes m2) (h1 : off1 + m1 ≤ n)
    (h_disj : disj_range (off1, off1 + m1) (off2, off2 + m2)) :
    (bs.write_subslice_at_index off2 sub2).subslice_with_length off1 m1 h1 =
      bs.subslice_with_length off1 m1 h1 := by
  ext i hi
  simp only [Bytes.subslice_with_length, Vector.getElem_ofFn, Bytes.write_subslice_at_index]
  split
  case isTrue h_in => exact False.elim (h_disj (off1 + i) (by omega) (by omega) h_in.1 h_in.2)
  case isFalse => rfl

private lemma foldl_tuple_subslice_not_mem {ts : List MType} (fo : Fin ts.length → Nat)
    (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (h_tuple : TupleValid fo (λ i ↦ (fl i).size_and_align) sa)
    (sub_fn : (idx : Fin ts.length) → Bytes (fl idx).size_and_align.size)
    (idx : Fin ts.length) :
    ∀ (idxs : List (Fin ts.length)) (_ : idx ∉ idxs) (acc : Bytes sa.size),
      (idxs.foldl (init := acc) λ bytes i ↦ bytes.write_subslice_at_index (fo i) (sub_fn i)).subslice_with_length
        (fo idx) (fl idx).size_and_align.size (h_tuple.size_bounds idx) =
      acc.subslice_with_length (fo idx) (fl idx).size_and_align.size (h_tuple.size_bounds idx)
  | [], _, _ => rfl
  | j :: js, h_not_mem, acc => by
    have h_ne : idx ≠ j := λ h ↦ h_not_mem (h ▸ List.mem_cons_self)
    have h_disj := h_tuple.fields_disj idx j h_ne
    rw [List.foldl_cons, foldl_tuple_subslice_not_mem fo fl sa h_tuple sub_fn idx js
          (λ h ↦ h_not_mem (List.mem_cons_of_mem j h))]
    exact subslice_write_subslice_disj acc (fo idx) (fo j) (sub_fn j) (h_tuple.size_bounds idx) h_disj

private lemma foldl_tuple_subslice_nodup {ts : List MType} (fo : Fin ts.length → Nat)
    (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (h_tuple : TupleValid fo (λ i ↦ (fl i).size_and_align) sa)
    (sub_fn : (idx : Fin ts.length) → Bytes (fl idx).size_and_align.size)
    (idx : Fin ts.length) :
    ∀ (idxs : List (Fin ts.length)), idxs.Nodup → idx ∈ idxs → ∀ (acc : Bytes sa.size),
      (idxs.foldl (init := acc) λ bytes i ↦ bytes.write_subslice_at_index (fo i) (sub_fn i)).subslice_with_length
        (fo idx) (fl idx).size_and_align.size (h_tuple.size_bounds idx) =
      sub_fn idx
  | j :: js, h_nodup, h_mem, acc => by
    rw [List.nodup_cons] at h_nodup
    rcases List.mem_cons.mp h_mem with rfl | h_in_js
    · rw [List.foldl_cons, foldl_tuple_subslice_not_mem fo fl sa h_tuple sub_fn idx js h_nodup.1]
      exact Bytes.subslice_write_subslice_self acc (fo idx) (sub_fn idx) (h_tuple.size_bounds idx)
    · exact foldl_tuple_subslice_nodup fo fl sa h_tuple sub_fn idx js h_nodup.2 h_in_js _

private lemma encode_tuple_subslice {ts : List MType} (fo : Fin ts.length → Nat)
    (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (h_tuple : TupleValid fo (λ i ↦ (fl i).size_and_align) sa)
    (values : List MVal) (hv : (MVal.tuple values).valid_for (.tuple ts))
    (idx : Fin ts.length) :
    let i : Fin values.length := ⟨idx.val, by rw [hv.tuple_len]; exact idx.isLt⟩
    (encode (.tuple fo fl sa) (.tuple values) hv).subslice_with_length
      (fo idx) (fl idx).size_and_align.size (h_tuple.size_bounds idx) =
    encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i) :=
  foldl_tuple_subslice_nodup fo fl sa h_tuple
    (λ k ↦ let i : Fin values.length := ⟨k.val, by rw [hv.tuple_len]; exact k.isLt⟩
           encode (fl k) values[i] (by simpa [i] using hv.tuple_proj i))
    idx (List.finRange ts.length) (List.nodup_finRange _) (List.mem_finRange idx) (Bytes.uninit sa.size)

private lemma encode_tuple_le_defined {ts : List MType} (fo : Fin ts.length → Nat)
    (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (bytes : Bytes sa.size) (values : List MVal) (hv : (MVal.tuple values).valid_for (.tuple ts))
    (h_bounds : ∀ idx : Fin ts.length, fo idx + (fl idx).size_and_align.size ≤ sa.size)
    (h_fields : ∀ idx : Fin ts.length,
      let i : Fin values.length := ⟨idx.val, by rw [hv.tuple_len]; exact idx.isLt⟩
      (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i)).le_defined
        (bytes.subslice_with_length (fo idx) (fl idx).size_and_align.size (h_bounds idx))) :
    (encode (.tuple fo fl sa) (.tuple values) hv).le_defined bytes := by
  suffices ∀ (idxs : List (Fin ts.length)) (acc : Bytes sa.size), acc.le_defined bytes →
      (idxs.foldl (init := acc) λ (bs : Bytes sa.size) (idx : Fin ts.length) ↦
        let i : Fin values.length := ⟨idx.val, by rw [hv.tuple_len]; exact idx.isLt⟩
        bs.write_subslice_at_index (fo idx) (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i))).le_defined bytes by
    exact this _ _ (λ j ↦ by rw [Bytes.uninit_getElem]; exact AbstractByte.le_defined_uninit _)
  intro idxs acc h_acc
  induction idxs generalizing acc with
  | nil => exact h_acc
  | cons idx tl ih =>
    apply ih
    intro j
    let i : Fin values.length := ⟨idx.val, by rw [hv.tuple_len]; exact idx.isLt⟩
    have h_step : (acc.write_subslice_at_index (fo idx) (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i)))[j.val] =
        if h : fo idx ≤ j.val ∧ j.val < fo idx + (fl idx).size_and_align.size then
          (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i))[j.val - fo idx]'(by omega)
        else acc[j.val] := by
      simp [Bytes.write_subslice_at_index]
    change (acc.write_subslice_at_index (fo idx) (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i)))[j.val].le_defined bytes[j.val]
    rw [h_step]
    split
    case isTrue hj =>
      have hf : (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i))[j.val - fo idx].le_defined
          (bytes.subslice_with_length (fo idx) (fl idx).size_and_align.size (h_bounds idx))[j.val - fo idx] :=
        h_fields idx ⟨j.val - fo idx, by omega⟩
      simpa [Bytes.subslice_with_length, show fo idx + (j.val - fo idx) = j.val by omega] using hf
    case isFalse => exact h_acc j

/-! ### Proofs of the Four Generic Representation Properties -/

theorem valid_decodeValid {ty : MType} (l : Layout ty) (hl : l.Valid) : l.DecodeValid := by
  induction hl with
  | int st =>
    intro bytes val h_dec
    simp only [decode, Option.bind_eq_bind] at h_dec
    cases h_data : bytes.toData with
    | none => rw [h_data] at h_dec; cases h_dec
    | some bytes_data =>
      rw [h_data] at h_dec; simp only [Option.bind_some, Option.some.injEq] at h_dec
      subst h_dec
      exact .int (Endianness.decode_can_repr st bytes_data)
  | tuple ts fo fl sa _ _ ih =>
    intro bytes val h_dec
    simp only [decode, Option.map_eq_some_iff] at h_dec
    obtain ⟨values, h_mapM, rfl⟩ := h_dec
    have h_len : values.length = ts.length := by
      simpa using list_mapM_eq_some_length h_mapM
    apply MVal.valid_for.tuple
    apply List.forall₂_iff_get.mpr ⟨h_len, λ i hi1 hi2 ↦ ?_⟩
    have h_item := list_mapM_finRange_eq_some h_mapM ⟨i, hi2⟩
    split at h_item
    case isFalse => cases h_item
    case isTrue h_bound =>
      exact ih ⟨i, hi2⟩ _ _ h_item
  | enum vs vt vl dc sa _ _ ih =>
    intro bytes val h_dec
    simp only [decode, Option.bind_eq_bind] at h_dec
    cases h_discr : decode_discriminant bytes dc with
    | none => rw [h_discr] at h_dec; cases h_dec
    | some d =>
      rw [h_discr] at h_dec; dsimp only [Option.bind_some] at h_dec
      split at h_dec
      case isFalse => cases h_dec
      case isTrue hd =>
        split at h_dec
        case isFalse => cases h_dec
        case isTrue hsz =>
          cases h_vdec : decode (vl ⟨d, hd⟩) (bytes.subslice_with_length 0 _ hsz) with
          | none => rw [h_vdec] at h_dec; cases h_dec
          | some v =>
            rw [h_vdec] at h_dec; simp only [Option.bind_some, Option.some.injEq] at h_dec
            subst h_dec
            exact .enum d v vs hd (ih ⟨d, hd⟩ _ _ h_vdec)

/-- Combines `decode` with a `DecodeValid` proof to return a subtype `{ val : MVal // val.valid_for ty }`. -/
def decode_valid {ty : MType} (l : Layout ty) (h_valid : l.DecodeValid)
    (bytes : Bytes l.size_and_align.size) : Option { val : MVal // val.valid_for ty } :=
  match h : decode l bytes with
  | none => none
  | some val => some ⟨val, h_valid bytes val h⟩

/-- Decodes `bytes` along a valid layout `hl : l.Valid`, coupling the decoded value with its typing proof. -/
def Valid.decode {ty : MType} {l : Layout ty} (hl : l.Valid)
    (bytes : Bytes l.size_and_align.size) : Option { val : MVal // val.valid_for ty } :=
  decode_valid l (valid_decodeValid l hl) bytes

theorem valid_decodeMono {ty : MType} (l : Layout ty) (hl : l.Valid) : l.DecodeMono := by
  induction hl with
  | int st =>
    intro bytes1 bytes2 h_le
    simp only [decode, Option.bind_eq_bind]
    cases h_data1 : bytes1.toData with
    | none => simp [Option.le_defined]
    | some data1 =>
      rw [← Bytes.eq_of_toData_some_le_defined h_data1 h_le, h_data1]
      rfl
  | tuple ts fo fl sa _ _ ih =>
    intro bytes1 bytes2 h_le
    apply Option.le_defined.map
    refine list_mapM_mono (List.finRange ts.length) λ idx _ ↦ ?_
    dsimp only; split
    case isFalse => trivial
    case isTrue h_bound =>
      exact ih idx _ _ (Bytes.subslice_le_defined h_le (fo idx) _ h_bound)
  | enum vs vt vl dc sa _ _ ih =>
    intro bytes1 bytes2 h_le
    simp only [decode]
    refine Option.le_defined.bind (decode_discriminant_mono h_le dc) λ d _ ↦ ?_
    split
    case isFalse => trivial
    case isTrue hd =>
      split
      case isFalse => trivial
      case isTrue hsz =>
        exact Option.le_defined.bind (ih ⟨d, hd⟩ _ _ (Bytes.subslice_le_defined h_le 0 _ hsz)) λ _ _ ↦ rfl

theorem valid_decodeEncode {ty : MType} (l : Layout ty) (hl : l.Valid) : l.DecodeEncode := by
  induction hl with
  | int st =>
    intro val hv
    cases val with
    | tuple _ | variant _ _ => cases hv
    | int i =>
      cases hv with
      | int h_repr =>
        simp only [encode, decode, Bytes.toData_map_init, Option.bind_eq_bind, Option.bind_some,
                   Endianness.decode_encode st i h_repr]
  | tuple ts fo fl sa _ h_tuple ih =>
    intro val hv
    cases val with
    | int _ | variant _ _ => cases hv
    | tuple values =>
      simp only [decode]
      rw [list_mapM_finRange_of_getElem (ys := values) hv.tuple_len]
      · rfl
      · intro idx
        rw [dif_pos (h_tuple.size_bounds idx)]
        rw [encode_tuple_subslice fo fl sa h_tuple values hv idx]
        exact ih idx _ _
  | enum vs vt vl dc sa h_vl_valid h_enum ih =>
    intro val hv
    cases val with
    | int _ | tuple _ => cases hv
    | variant d data =>
      let idx : Fin vs.length := ⟨d, hv.variant_bound⟩
      let payload_bs := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (vl idx) data hv.variant_proj)
      let encode_bs : Bytes (Layout.enum vt vl dc sa).size_and_align.size :=
        encode_discriminant payload_bs (vt idx)
      change decode (.enum vt vl dc sa) encode_bs = some (.variant d data)
      simp only [decode, Option.bind_eq_bind]
      have h_discr : decode_discriminant encode_bs dc = some d :=
        h_enum.discr_complete idx data hv.variant_proj
      rw [h_discr]; dsimp only [Option.bind_some]
      rw [dif_pos hv.variant_bound]
      have hsz : 0 + (vl idx).size_and_align.size ≤ sa.size := by rw [h_enum.data_sizes idx]; omega
      rw [dif_pos hsz]
      have h_dec_payload :
          decode (vl idx) (payload_bs.subslice_with_length 0 (vl idx).size_and_align.size hsz) = some data := by
        rw [Bytes.subslice_write_subslice_self _ 0 _ hsz]; exact ih idx data hv.variant_proj
      have h_le_sub :
          (payload_bs.subslice_with_length 0 (vl idx).size_and_align.size hsz).le_defined
            (encode_bs.subslice_with_length 0 (vl idx).size_and_align.size hsz) :=
        Bytes.subslice_le_defined (h_enum.tags_preserve_payload idx data hv.variant_proj) 0 _ hsz
      have h_mono := valid_decodeMono (vl idx) (h_vl_valid idx) _ _ h_le_sub
      rw [h_dec_payload] at h_mono
      rw [Option.le_defined.eq_of_some h_mono]; rfl

theorem valid_encodeDecodeLeDefined {ty : MType} (l : Layout ty) (hl : l.Valid) : l.EncodeDecodeLeDefined := by
  induction hl with
  | int st =>
    intro bytes val hv h_dec
    cases val with
    | tuple _ | variant _ _ => cases hv
    | int i =>
      simp only [decode, Option.bind_eq_bind] at h_dec
      cases h_data : bytes.toData with
      | none => rw [h_data] at h_dec; cases h_dec
      | some bytes_data =>
        rw [h_data] at h_dec; simp only [Option.bind_some, Option.some.injEq, MVal.int.injEq] at h_dec
        subst h_dec
        have h_eq : encode .int (.int (Endianness.decode st bytes_data)) hv = bytes := by
          ext k hk
          simp only [encode, Vector.getElem_map, Endianness.encode_decode st bytes_data]
          exact (Bytes.getElem_of_toData h_data k hk).symm
        rw [h_eq]; exact Bytes.le_defined_refl bytes
  | tuple ts fo fl sa _ h_tuple ih =>
    intro bytes val hv h_dec
    cases val with
    | int _ | variant _ _ => cases hv
    | tuple values =>
      simp only [decode, Option.map_eq_some_iff] at h_dec
      obtain ⟨dec_values, h_mapM, h_eq⟩ := h_dec
      injection h_eq with h_eq; subst h_eq
      apply encode_tuple_le_defined fo fl sa bytes dec_values hv h_tuple.size_bounds
      intro idx
      have h_item := list_mapM_finRange_eq_some h_mapM idx
      rw [dif_pos (h_tuple.size_bounds idx)] at h_item
      exact ih idx _ _ _ h_item
  | enum vs vt vl dc sa _ h_enum ih =>
    intro bytes val hv h_dec
    cases val with
    | int _ | tuple _ => cases hv
    | variant d data =>
      simp only [decode, Option.bind_eq_bind] at h_dec
      cases h_discr : decode_discriminant bytes dc with
      | none => rw [h_discr] at h_dec; cases h_dec
      | some d_dec =>
        rw [h_discr] at h_dec; dsimp only [Option.bind_some] at h_dec
        split at h_dec
        case isFalse => cases h_dec
        case isTrue hd =>
          split at h_dec
          case isFalse => cases h_dec
          case isTrue hsz =>
            cases h_vdec : decode (vl ⟨d_dec, hd⟩) (bytes.subslice_with_length 0 _ hsz) with
            | none => rw [h_vdec] at h_dec; cases h_dec
            | some v_dec =>
              rw [h_vdec] at h_dec
              simp only [Option.bind_some, Option.some.injEq, MVal.variant.injEq] at h_dec
              obtain ⟨rfl, rfl⟩ := h_dec
              let idx : Fin vs.length := ⟨d_dec, hd⟩
              let payload_bs := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (vl idx) v_dec hv.variant_proj)
              have h_vle := ih idx _ v_dec hv.variant_proj h_vdec
              have h_pay_le : payload_bs.le_defined bytes := λ k ↦ by
                have h_ksz : k.val < (vl idx).size_and_align.size := by rw [h_enum.data_sizes idx]; exact k.isLt
                have hf : (encode (vl idx) v_dec hv.variant_proj)[k.val].le_defined
                    (bytes.subslice_with_length 0 _ hsz)[k.val] := h_vle ⟨k.val, h_ksz⟩
                simp only [Bytes.subslice_with_length, Vector.getElem_ofFn, Nat.zero_add] at hf
                rw [Bytes.write_subslice_at_index_zero_lt _ _ h_ksz]
                exact hf
              exact encode_discriminant_le_defined payload_bs bytes (vt idx) h_pay_le
                (h_enum.discr_tags_le_defined bytes idx h_discr)

/-! ## Canonical Witness Layout Construction -/

namespace Example

open SizeAndAlign

def finMax : (n : Nat) → (Fin n → Nat) → Nat → Nat
  | 0, _, init => init
  | n + 1, f, init => max (f 0) (finMax n (λ i ↦ f i.succ) init)

lemma init_le_finMax : ∀ n (f : Fin n → Nat) init, init ≤ finMax n f init
  | 0, _, _ => Nat.le_refl _
  | n + 1, _, init => Nat.le_trans (init_le_finMax n _ init) (Nat.le_max_right _ _)

lemma le_finMax : ∀ n (f : Fin n → Nat) init (i : Fin n), f i ≤ finMax n f init
  | _ + 1, _, _, ⟨0, _⟩ => Nat.le_max_left _ _
  | n + 1, f, init, ⟨i + 1, hi⟩ => Nat.le_trans (le_finMax n (λ k ↦ f k.succ) init ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (Nat.le_max_right _ _)

lemma finMax_isPowerOfTwo : ∀ n (f : Fin n → Nat) init,
    init.isPowerOfTwo → (∀ i, (f i).isPowerOfTwo) → (finMax n f init).isPowerOfTwo
  | 0, _, _, h0, _ => h0
  | n + 1, f, init, h0, hf => by
    by_cases h : f 0 ≤ finMax n (λ i ↦ f i.succ) init <;>
      [simp [finMax, Nat.max_eq_right h, finMax_isPowerOfTwo n _ init h0 (λ i ↦ hf i.succ)];
       simp [finMax, Nat.max_eq_left (Nat.le_of_not_le h), hf 0]]

private lemma encode_tuple_prefix_uninit {ts : List MType}
    (fo : Fin ts.length → Nat) (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (prefix_len : Nat) (hoff : ∀ idx : Fin ts.length, prefix_len ≤ fo idx)
    (v : MVal) (hv : v.valid_for (.tuple ts)) {j : Fin sa.size} (hlt : j.val < prefix_len) :
    (encode (.tuple fo fl sa) v hv)[j.val] = .uninit := by
  cases v with
  | int _ | variant _ _ => cases hv
  | tuple values =>
    suffices ∀ (idxs : List (Fin ts.length)) (acc : Bytes sa.size),
        (idxs.foldl (init := acc) λ (bytes : Bytes sa.size) (idx : Fin ts.length) ↦
          let i : Fin values.length := ⟨idx.val, by rw [hv.tuple_len]; exact idx.isLt⟩
          bytes.write_subslice_at_index (fo idx) (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i)))[j] = acc[j] by
      exact (this _ _).trans (Bytes.uninit_getElem sa.size j)
    intro idxs acc; induction idxs generalizing acc with
    | nil => rfl
    | cons hd _ ih => exact (ih _).trans (Bytes.write_subslice_at_index_lt acc _ _ (Nat.lt_of_lt_of_le hlt (hoff hd)))

/-- Pads a tuple variant layout so its size and alignment match `sa`, shifting field offsets
    right by `sa.align` so that prefix bytes `[0 ..< sa.align)` remain `.uninit`. -/
def padVariantLayout {t : MType} (ht : t.isTuple) (cl : { l : Layout t // l.Valid }) (sa : SizeAndAlign)
    (h_size : cl.1.size_and_align.size + sa.align ≤ sa.size) (h_align : cl.1.size_and_align.align ≤ sa.align) :
    { l : Layout t // l.Valid ∧ l.size_and_align = sa ∧
        ∀ (v : MVal) (hv : v.valid_for t) (j : Nat) (hj : j < l.size_and_align.size),
          j < sa.align → (encode l v hv)[j] = .uninit } :=
  match t, ht, cl with
  | .int _, h, _ | .enum _, h, _ => nomatch h
  | .tuple ts, _, ⟨.tuple vfo vfl _, h_valid⟩ =>
    ⟨.tuple (λ j ↦ sa.align + vfo j) vfl sa, by
      cases h_valid with
      | tuple _ _ _ _ h_vfl_valid h_vtuple =>
        exact ⟨.tuple ts _ vfl sa h_vfl_valid
          ⟨by dsimp only; intro i1 i2 hne n h1 h2 h3 h4
              have hdisj := h_vtuple.fields_disj; dsimp only at hdisj
              exact hdisj i1 i2 hne (n - sa.align) (by omega) (by omega) (by omega) (by omega),
           λ j ↦ Nat.le_trans (h_vtuple.fields_aligned j) h_align,
           λ j ↦ by have := h_vtuple.size_bounds j; dsimp [Layout.size_and_align] at h_size; omega,
           λ j ↦ Nat.dvd_add
             (dvd_of_isPowerOfTwo_le (vfl j).size_and_align.wf_align sa.wf_align (Nat.le_trans (h_vtuple.fields_aligned j) h_align))
             (h_vtuple.offs_aligned j)⟩,
          rfl, λ v hv j hj hlt ↦ encode_tuple_prefix_uninit _ vfl sa sa.align (λ _ ↦ Nat.le_add_right _ _) v hv (j := ⟨j, hj⟩) hlt⟩⟩

/-- Builds a valid canonical tuple layout from valid layouts for its field types. -/
def mkTuple (ts : List MType) (child_layouts : (idx : Fin ts.length) → { l : Layout ts[idx] // l.Valid }) :
    { l : Layout (.tuple ts) // l.Valid } :=
  let fl : (idx : Fin ts.length) → Layout ts[idx] := λ idx ↦ (child_layouts idx).1
  let fsa : Fin ts.length → SizeAndAlign := λ idx ↦ (fl idx).size_and_align
  let A := finMax ts.length (λ i ↦ (fsa i).align) 1
  let hA : A.isPowerOfTwo := finMax_isPowerOfTwo ts.length _ 1 Nat.isPowerOfTwo_one (λ i ↦ (fsa i).wf_align)
  let S := (finMax ts.length (λ i ↦ (fsa i).size) 0 + A - 1) / A
  let sa : SizeAndAlign := ⟨(ts.length * S) * A, A, hA, Nat.dvd_mul_left A _⟩
  have h_end_le : ∀ i : Fin ts.length, (i.val * S) * A + (fsa i).size ≤ ((i.val + 1) * S) * A := λ i ↦ by
    have : (fsa i).size ≤ S * A := Nat.le_trans (le_finMax _ (λ j ↦ (fsa j).size) 0 i) (le_alignUp _ (Nat.pos_of_isPowerOfTwo hA))
    rw [Nat.add_one_mul, Nat.add_mul]; omega
  have h_lt : ∀ {i1 i2 : Fin ts.length}, i1 < i2 → (i1.val * S) * A + (fsa i1).size ≤ (i2.val * S) * A :=
    λ hlt ↦ Nat.le_trans (h_end_le _) (Nat.mul_le_mul_right A (Nat.mul_le_mul_right S hlt))
  ⟨.tuple (λ i ↦ (i.val * S) * A) fl sa,
   .tuple ts _ fl sa (λ idx ↦ (child_layouts idx).2)
     ⟨by dsimp only; intro i1 i2 hne n h1 h2 h3 h4
         rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h <;>
           [have := h_lt h; have := h_lt h] <;> dsimp only [fsa] at this <;> omega,
      λ i ↦ le_finMax _ (λ j ↦ (fsa j).align) 1 i,
      λ i ↦ Nat.le_trans (h_end_le i) (Nat.mul_le_mul_right A (Nat.mul_le_mul_right S i.isLt)),
      λ i ↦ Nat.dvd_trans (dvd_of_isPowerOfTwo_le (fsa i).wf_align hA (le_finMax _ (λ j ↦ (fsa j).align) 1 i)) (Nat.dvd_mul_left A _)⟩⟩

/-- Builds a valid canonical enum layout from valid layouts for its tuple variants. -/
def mkEnum (vs : List MType) (h_max : vs.length ≤ Std.Usize.max) (ht : ∀ idx : Fin vs.length, vs[idx].isTuple)
    (child_layouts : (idx : Fin vs.length) → { l : Layout vs[idx] // l.Valid }) :
    { l : Layout (.enum vs) // l.Valid } :=
  let fsa : Fin vs.length → SizeAndAlign := λ idx ↦ (child_layouts idx).1.size_and_align
  let tagTy : IUScalarTy := .unsigned .Usize
  let A := finMax vs.length (λ i ↦ (fsa i).align) tagTy.size_and_align.align
  let hA : A.isPowerOfTwo := finMax_isPowerOfTwo vs.length _ _ tagTy.size_and_align.wf_align (λ i ↦ (fsa i).wf_align)
  let S := (finMax vs.length (λ i ↦ (fsa i).size) 0 + A - 1) / A
  let sa : SizeAndAlign := ⟨(S + 1) * A, A, hA, Nat.dvd_mul_left A (S + 1)⟩
  let vl_padded := λ idx ↦ padVariantLayout (ht idx) (child_layouts idx) sa
    (by have : (fsa idx).size ≤ S * A := Nat.le_trans (le_finMax _ (λ j ↦ (fsa j).size) 0 idx) (le_alignUp _ (Nat.pos_of_isPowerOfTwo hA))
        have := Nat.add_one_mul S A; dsimp [fsa, sa] at *; omega)
    (le_finMax _ (λ i ↦ (fsa i).align) _ idx)
  let vl : (idx : Fin vs.length) → Layout vs[idx] := λ idx ↦ (vl_padded idx).1
  let vt : Fin vs.length → List TagToWrite := λ idx ↦ [⟨0, tagTy, ⟨BitVec.ofNat tagTy.numBits idx.val⟩⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  have hTagLeAlign : tagTy.size_and_align.size ≤ sa.align := init_le_finMax vs.length (λ i ↦ (fsa i).align) tagTy.size_and_align.align
  have hTagBounds : 0 + tagTy.size_and_align.size ≤ sa.size := by have := Nat.le_mul_of_pos_left A (Nat.succ_pos S); dsimp [sa] at *; omega
  ⟨.enum vt vl discr sa, .enum vs vt vl discr sa (λ idx ↦ (vl_padded idx).2.1)
    ⟨λ idx ↦ by rw [(vl_padded idx).2.2.1], λ idx ↦ by rw [(vl_padded idx).2.2.1],
     .read 0 tagTy _ ⟨hTagBounds, Nat.dvd_zero _⟩ (λ _ ↦ by split <;> [exact .known _ ‹_›; exact .invalid]),
     -- 1. `tags_preserve_payload`: tag writes into `[0 ..< tag_sz) ⊆ [0 ..< sa.align)`, which is `.uninit`.
     by intro idx v hv payload_bs k
        dsimp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv]
        by_cases hk : k.val < tagTy.size_and_align.size
        · have h_vsz : k.val < (vl idx).size_and_align.size := by rw [(vl_padded idx).2.2.1]; omega
          rw [Bytes.write_subslice_at_index_zero_lt _ _ h_vsz,
              (vl_padded idx).2.2.2 v hv k.val h_vsz (Nat.lt_of_lt_of_le hk hTagLeAlign)]
          exact AbstractByte.le_defined_uninit _
        · rw [Bytes.write_subslice_at_index_zero_ge _ _ (Nat.le_of_not_lt hk)]; exact AbstractByte.le_defined_refl _,
     -- 2. `discr_complete`: reading `tagTy` back from `[0 ..< tag_sz)` recovers `idx.val`.
     by intro idx v hv
        dsimp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, discr, IUScalar.bv]
        unfold decode_discriminant; rw [dif_pos hTagBounds]
        simp only [Bytes.subslice_write_subslice_zero, Bytes.toData_map_init, Option.bind_eq_bind, Option.bind_some,
                   Endianness.decode_bitvec_encode_bitvec]
        have h_lt_max : idx.val < 2 ^ tagTy.numBits := by
          have : Std.Usize.max < 2 ^ tagTy.numBits := by
            rcases System.Platform.numBits_eq with h | h <;> simp [Std.Usize.max, Std.Usize.numBits, tagTy, IUScalarTy.numBits, Std.UScalarTy.numBits, h]
          omega
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt_max, if_pos idx.isLt]; rfl,
     -- 3. `discr_tags_le_defined`: if `decode_discriminant bytes discr = some idx.val`, `bytes[0 ..< tag_sz)` matches `vt idx`.
     by intro bytes idx h_dec
        dsimp only [discr] at h_dec; unfold decode_discriminant at h_dec; rw [dif_pos hTagBounds] at h_dec
        dsimp only [Option.bind_eq_bind] at h_dec
        cases h_data : (bytes.subslice_with_length 0 tagTy.size_and_align.size hTagBounds).toData with
        | none => simp [h_data] at h_dec
        | some bytes_data =>
          rw [h_data] at h_dec; dsimp only [Option.bind_some] at h_dec
          have h_nat : (Endianness.decode_bitvec tagTy bytes_data).toNat = idx.val := by split at h_dec <;> [injection h_dec; cases h_dec]
          have h_tag_vec : Endianness.encode_bitvec tagTy.size_and_align.size (BitVec.ofNat tagTy.numBits idx.val) = bytes_data := by
            rw [show BitVec.ofNat tagTy.numBits idx.val = Endianness.decode_bitvec tagTy bytes_data by rw [← h_nat, BitVec.ofNat_toNat]; simp]
            exact Endianness.encode_bitvec_decode_bitvec tagTy bytes_data
          dsimp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv]; rw [h_tag_vec]
          intro k
          by_cases hk : k.val < tagTy.size_and_align.size
          · rw [Bytes.write_subslice_at_index_zero_lt _ _ hk]
            rw [show bytes[k] = .init bytes_data[k.val] from by simpa [Bytes.subslice_with_length] using Bytes.getElem_of_toData h_data k.val hk]
            simp
          · rw [Bytes.write_subslice_at_index_zero_ge _ _ (Nat.le_of_not_lt hk)]; simp [Bytes.uninit]⟩⟩

/-- Canonical layout constructor for any `Reasonable` `MType`. -/
def mk (ty : MType) {hr : ty.Reasonable} : { l : Layout ty // l.Valid } :=
  match ty with
  | .int ty => ⟨.int, .int ty⟩
  | .tuple ts => mkTuple ts λ idx ↦ mk ts[idx] (hr := by cases hr with | tuple _ h => exact h idx)
  | .enum vs => mkEnum vs (by cases hr with | enum _ h _ _ => exact h) (by cases hr with | enum _ _ ht _ => exact ht)
                  λ idx ↦ mk vs[idx] (hr := by cases hr with | enum _ _ _ h => exact h idx)
termination_by sizeOf ty
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem (List.getElem_mem idx.isLt); omega

end Example

end Layout

end Aeneas
