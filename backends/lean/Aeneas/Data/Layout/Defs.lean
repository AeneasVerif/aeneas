module
public import Aeneas.Data.Byte
public import Aeneas.Data.BitVec
public import Aeneas.Data.Layout.Prelims
public import Aeneas.Data.Layout.Bytes
public import Aeneas.Data.Layout.MTypes
@[expose] public section

namespace Aeneas

/-! ## Size and Alignment -/

structure SizeAndAlign : Type 0 where
  size : Nat
  align : Nat
  wf_align : align.isPowerOfTwo
  wf_size : align ∣ size

lemma SizeAndAlign.grind_wf_align (sa : SizeAndAlign) : sa.align.isPowerOfTwo := sa.wf_align
grind_pattern SizeAndAlign.grind_wf_align => sa.align

lemma SizeAndAlign.grind_wf_size (sa : SizeAndAlign) : sa.align ∣ sa.size := sa.wf_size
grind_pattern SizeAndAlign.grind_wf_size => sa.size

namespace SizeAndAlign

lemma num_bytes_is_power_of_two {ty : IUScalarTy} : (ty.numBits / 8).isPowerOfTwo := by
  rcases ty with ⟨ty⟩ | ⟨ty⟩ <;>
    cases ty <;>
    rcases System.Platform.numBits_eq with h | h <;>
    simp [IUScalarTy.numBits, Std.IScalarTy.numBits, Std.UScalarTy.numBits, h] <;>
    decide

lemma align_pos (sa : SizeAndAlign) : 0 < sa.align :=
  Nat.pos_of_isPowerOfTwo sa.wf_align
grind_pattern align_pos => sa.align

end SizeAndAlign

def SizeAndAlign.ValidForScalar (sa : SizeAndAlign) (ty : IUScalarTy) : Prop :=
  sa.size = ty.numBits / 8

def IUScalarTy.size (ty : IUScalarTy) : Nat := ty.numBits / 8

def IUScalarTy.reasonablyAligned (ty : IUScalarTy) : SizeAndAlign :=
  ⟨ty.size, ty.size, SizeAndAlign.num_bytes_is_power_of_two, by simp⟩

lemma IUScalarTy.reasonablyAligned_isReasonable {ty : IUScalarTy} : ty.reasonablyAligned.ValidForScalar ty := by rfl

noncomputable def IUScalarTy.size_and_align (ty : IUScalarTy) : SizeAndAlign :=
  @Classical.choose SizeAndAlign (·.ValidForScalar ty) ⟨_, ty.reasonablyAligned_isReasonable⟩

@[simp, grind =] lemma IUScalarTy.knownSize {ty : IUScalarTy} : ty.size_and_align.size = ty.size :=
  @Classical.choose_spec SizeAndAlign (·.ValidForScalar ty) ⟨_, ty.reasonablyAligned_isReasonable⟩

@[simp, grind →] lemma SizeAndAlign.sizeOneAlignOne (sa : SizeAndAlign) : sa.size = 1 → sa.align = 1 := by
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

@[simp, grind =] def SizeAndAlign.zero_sized_minimally_aligned : SizeAndAlign :=
  ⟨0, 1, by grind, by grind⟩

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
      (field_offs : (idx : Nat) → idx < ts.length → Nat)
      -- NB: Lean is sensitive to the specifics of this inductive definition.
      -- For example, merging `field_layouts` and `field_offs` into one function
      -- returning a pair is not possible, as that prevents Lean from seeing that
      -- the inductive is strictly positive.
      (field_layouts : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
      (sa : SizeAndAlign) :
      Layout (.tuple ts f)
  | enum
      (variant_tags : (idx : Nat) → idx < vs.length → List TagToWrite)
      (variant_layouts : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (discr : Discriminator)
      (sa : SizeAndAlign) :
      Layout (.enum vs f)

namespace Layout

@[implicit_reducible]
def size : {ty : MType} → Layout ty → Nat
  | .int ty, .int => ty.size
  | _, .tuple _ _ sa => sa.size
  | _, .enum _ _ _ sa => sa.size

noncomputable def size_and_align : {ty : MType} → Layout ty → SizeAndAlign
  | .int ty, .int => ty.size_and_align
  | _, .tuple _ _ sa => sa
  | _, .enum _ _ _ sa => sa

@[simp, grind =] lemma size_known (l : Layout ty) : l.size_and_align.size = l.size :=
  by cases l <;> simp [size, size_and_align]

grind_pattern size_known => l.size_and_align
grind_pattern size_known => l.size

@[simp, grind =] lemma int_size (ty : IUScalarTy) : (@Layout.int ty).size = ty.size := rfl
@[simp, grind =] lemma tuple_size {ts f} fo fl sa : (@Layout.tuple ts f fo fl sa).size = sa.size := rfl
@[simp, grind =] lemma enum_size {vs f} vt vl d sa : (@Layout.enum vs f vt vl d sa).size = sa.size := rfl

@[simp, grind =] lemma int_size_and_align (ty : IUScalarTy) : (@Layout.int ty).size_and_align = ty.size_and_align := rfl
@[simp, grind =] lemma tuple_size_and_align ty f ts fo sa : (@Layout.tuple ty f ts fo sa).size_and_align = sa := rfl
@[simp, grind =] lemma enum_size_and_align ty f vt vl d sa : (@Layout.enum ty f vt vl d sa).size_and_align = sa := rfl

end Layout

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
  | .int st, .int, .int i, h =>
    (Endianness.encode st i (by grind)).map .init
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

end Layout

/-! ## Layout Validity -/

@[grind]
structure Layout.ScalarValidAt (st : IUScalarTy) (off : Nat) (sa : SizeAndAlign) where
  in_bounds : off + st.size ≤ sa.size

@[grind =]
def TagToWrite.Valid (t : TagToWrite) (sa : SizeAndAlign) :=
  Layout.ScalarValidAt t.ty t.offset sa

@[grind]
inductive Discriminator.Valid (sa : SizeAndAlign) (n : Nat) : Discriminator → Prop where
  | known d : d < n → Discriminator.Valid _ _ (.known d)
  | invalid : Discriminator.Valid _ _ .invalid
  | read off ty matcher :
      Layout.ScalarValidAt ty off sa →
      (∀ idx, (matcher idx).Valid sa n) →
      Discriminator.Valid _ _ (.read off ty matcher)

namespace Layout

@[grind =]
def disj_range (r1 r2 : Nat × Nat) : Prop :=
  ∀ n, r1.1 ≤ n → n < r1.2 → r2.1 ≤ n → n < r2.2 → False

@[grind]
structure TupleValid (n : Nat) (field_offs : (idx : Nat) → idx < n → Nat)
    (field_sizes : (idx : Nat) → idx < n → Nat) (sa : SizeAndAlign) where
  fields_disj :
    ∀ (i1 i2 : Nat) (hi1 : i1 < n) (hi2 : i2 < n), i1 ≠ i2 →
      disj_range (field_offs i1 hi1, field_offs i1 hi1 + field_sizes i1 hi1)
                 (field_offs i2 hi2, field_offs i2 hi2 + field_sizes i2 hi2)
  size_bounds : ∀ (i : Nat) (hi : i < n), sa.size ≥ field_offs i hi + field_sizes i hi

structure EnumValid {vs : List MType}
      (variant_tags : (idx : Nat) → idx < vs.length → List TagToWrite)
      (variant_layouts : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (discr : Discriminator)
      (sa : SizeAndAlign) where
  data_sizes : ∀ idx (h : idx < vs.length), (variant_layouts idx h).size = sa.size
  data_aligns : ∀ idx (h : idx < vs.length), (variant_layouts idx h).size_and_align.align ≤ sa.align
  taggers_valid : ∀ idx (h : idx < vs.length), (variant_tags idx h).Forall (·.Valid sa)
  discriminator_valid : discr.Valid sa vs.length
  /-- Writing variant `idx`'s tags into the bytes around the data does not clobber any
      initialized byte written by `variant_layouts idx`. -/
  tags_preserve_payload : ∀ (idx : Nat) (h : idx < vs.length) (v : MVal) (hv : v.valid_for vs[idx]),
    let payload_bs := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (variant_layouts idx h) v hv)
    payload_bs.le_defined (encode_discriminant payload_bs (variant_tags idx h))
  /-- `decode_discriminant` recovers `idx` on any valid encoded payload + tags for variant `idx`. -/
  discr_complete : ∀ (idx : Nat) (h : idx < vs.length) (v : MVal) (hv : v.valid_for vs[idx]),
    let payload_bs := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (variant_layouts idx h) v hv)
    decode_discriminant (encode_discriminant payload_bs (variant_tags idx h)) discr = some idx
  /-- Whenever `decode_discriminant` selects variant `idx`, all tag bytes written by `variant_tags idx`
      are less-or-equally-defined as `bytes`. -/
  discr_tags_le_defined : ∀ (bytes : Bytes sa.size) (idx : Nat) (h : idx < vs.length),
    decode_discriminant bytes discr = some idx →
    (encode_discriminant (Bytes.uninit sa.size) (variant_tags idx h)).le_defined bytes

inductive Valid : {ty : MType} → Layout ty → Prop where
  | int ty : Valid (.int : Layout (.int ty))
  | tuple ts f fo fl sa :
      (∀ idx (h : idx < ts.length), (fl idx h).Valid) →
      TupleValid ts.length fo (λ i hi ↦ (fl i hi).size) sa →
      Valid (.tuple fo fl sa : Layout (.tuple ts f))
  | enum vs f vt vl dc sa :
      (∀ idx (h : idx < vs.length), (vl idx h).Valid) →
      EnumValid vt vl dc sa →
      Valid (.enum vt vl dc sa : Layout (.enum vs f))

/-! ## Generic Representation Properties (Galois Connection)
    Following MiniRust's `spec/lang/representation.md` ("Generic properties"). -/

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

/-! ## Extra Properties that might be imposed on a layout -/

@[grind]
structure TupleReasonablyAligned (n : Nat) (field_offs : (idx : Nat) → idx < n → Nat)
    (field_layouts : (idx : Nat) → idx < n → SizeAndAlign) (sa : SizeAndAlign) where
  fields_aligned : ∀ i (hi : i < n), sa.align ≥ (field_layouts i hi).align
  offs_aligned : ∀ i (hi : i < n), (field_layouts i hi).align ∣ field_offs i hi

--- A reasonably aligned layout is one that guaranees the fields are at "well-aligned" positions.
--- In other words, it is not repr(packed).
--- This is a non-recursive property, since this does not affect the layout of the contained fields
inductive ReasonablyAligned : {ty : MType} → Layout ty → Prop where
  | int ty : ReasonablyAligned (.int : Layout (.int ty))
  | tuple ts f fo fl sa :
      TupleReasonablyAligned ts.length fo (λ i hi ↦ (fl i hi).size_and_align) sa →
      ReasonablyAligned (.tuple fo fl sa : Layout (.tuple ts f))
  | enum vs f vt vl dc sa :
      -- It is intended that this recurses here, to control the layout of each variant.
      (∀ idx (h : idx < vs.length), (vl idx h).ReasonablyAligned) →
      ReasonablyAligned (.enum vt vl dc sa : Layout (.enum vs f))

inductive Transparent : {ty : MType} → Layout ty → Prop where
| tuple_zero_sized ts f fo fl :
    (∀ idx (h : idx < ts.length), (fl idx h).size_and_align = .zero_sized_minimally_aligned) →
    Transparent (.tuple fo fl .zero_sized_minimally_aligned : Layout (.tuple ts f))
| tuple_one_elem ts f fo fl idnz (hidnz : idnz < ts.length) :
    fo idnz hidnz = 0 →
    (∀ idx (h : idx < ts.length), idx ≠ idnz → (fl idx h).size_and_align = .zero_sized_minimally_aligned) →
    Transparent (.tuple fo fl (fl idnz hidnz).size_and_align : Layout (.tuple ts f))
| enum v f (vl : Layout v) :
    Transparent vl →
    Transparent (.enum (λ _ _ ↦ []) (λ | 0, _ => vl) (.known 0) vl.size_and_align : Layout (.enum [v] f))

inductive Packed (n : Nat) : {ty : MType} → Layout ty → Prop where
| tuple ts f fo fl (ford : Fin ts.length → Fin ts.length) sa :
    n.isPowerOfTwo →
    sa.align ≤ n →
    -- we have a bijection telling us the field order
    Function.Bijective ford →
    -- each field's offset is determined by the previous field using `alignUp`
    (∀ i, (hle : i + 1 < ts.length) →
      let cur := (ford ⟨i, by grind⟩);
      let nxt := (ford ⟨i + 1, hle⟩)
      fo nxt (by grind) = alignUp
        (fo cur (by grind) + (fl cur (by grind)).size)
        (min n (fl nxt (by grind)).size_and_align.align)) →
    -- the first field is at offset 0
    ((hl : ts.length > 0) → fo (ford ⟨0, by grind⟩) (by grind) = 0) →
    -- there is no extra padding at the end
    sa.size = natMax ts.length (λ x hx ↦ alignUp ((fo x hx) + (fl x hx).size) sa.align) 0 →
    -- our alignment upper-bounds the fields
    (∀ i (hi : i < ts.length), min n (fl i hi).size_and_align.align ≤ sa.align) →
    Packed n (.tuple fo fl sa : Layout (.tuple ts f))

structure Aligned (n : Nat) {ty : MType} (l : Layout ty) : Prop where
  n_wf : n.isPowerOfTwo
  aligned : l.size_and_align.align ≥ n

@[grind .]
lemma Transparent_ReasonablyAligned ty (l : Layout ty) : l.Transparent → l.ReasonablyAligned
  | .tuple_zero_sized ts f fo fl h =>
    .tuple ts f fo fl .zero_sized_minimally_aligned ⟨by grind, by intro i hi; simp [h i hi]⟩
  | .tuple_one_elem ts f fo fl idnz hidnz h0 h =>
    .tuple ts f fo fl (fl idnz hidnz).size_and_align
      ⟨by grind,
       by intro i hi
          by_cases heq : i = idnz
          · subst heq; simp [h0]
          · simp [h i hi heq]⟩
  | .enum v f vl hvl =>
    .enum [v] f _ _ _ _ (λ | 0, _ => Transparent_ReasonablyAligned v vl hvl)

def alignTupleUp {ts f} (l : Layout (.tuple ts f)) (a : Nat) (ha : a.isPowerOfTwo) : Layout (.tuple ts f) := match ts, l with
| ts, .tuple fo fl sa =>
    let na := max sa.align a;
    let ns := alignUp sa.size na;
    .tuple fo fl ⟨ns, na, by grind, by grind⟩

def alignEnumUp {vs f} (l : Layout (.enum vs f)) (a : Nat) (ha : a.isPowerOfTwo) (ht : vs.Forall MType.isTuple) : Layout (.enum vs f) := match vs, l with
| vs, .enum vt vl d sa =>
    let na := max sa.align a;
    let ns := alignUp sa.size na;
    .enum vt (λ i hi ↦ match vs[i], vl i hi with
      | .tuple ts _, x => x.alignTupleUp a ha
      | _, x  => x -- vacuous case
    ) d ⟨ns, na, by grind, by grind⟩

@[grind ←]
lemma alignTupleUp_reasonablyAligned {ts f} (l : Layout (.tuple ts f)) (a : Nat) (ha : a.isPowerOfTwo)
    (h : l.ReasonablyAligned) : (l.alignTupleUp a ha).ReasonablyAligned :=
  match ts, l, h with
  | ts, .tuple fo fl sa, .tuple _ _ _ _ _ h_tup =>
    .tuple ts f fo fl _ ⟨by grind, h_tup.offs_aligned⟩

@[grind ←]
lemma alignEnumUp_reasonablyAligned {vs f} (l : Layout (.enum vs f)) (a : Nat) (ha : a.isPowerOfTwo)
    (ht : vs.Forall MType.isTuple) (h : l.ReasonablyAligned) :
    (l.alignEnumUp a ha ht).ReasonablyAligned :=
  match vs, l, h with
  | vs, .enum vt vl d sa, .enum _ _ _ _ _ _ h_vl =>
    .enum vs f vt _ d _ (λ i hi ↦
      match vs[i], vl i hi, h_vl i hi with
      | .tuple _ _, x, hx => alignTupleUp_reasonablyAligned x a ha hx
      | .int _, _, hx | .enum _ _, _, hx => hx)

@[grind ←]
lemma alignTupleUp_aligned {ts f} (l : Layout (.tuple ts f)) (a : Nat) (ha : a.isPowerOfTwo) :
    (l.alignTupleUp a ha).Aligned a :=
  match ts, l with
  | _, .tuple _ _ _ => ⟨ha, by simp [alignTupleUp, size_and_align]⟩

@[grind ←]
lemma alignEnumUp_aligned {vs f} (l : Layout (.enum vs f)) (a : Nat) (ha : a.isPowerOfTwo)
    (ht : vs.Forall MType.isTuple) :
    (l.alignEnumUp a ha ht).Aligned a :=
  match vs, l with
  | _, .enum _ _ _ _ => ⟨ha, by simp [alignEnumUp, size_and_align]⟩

end Layout

end Aeneas
