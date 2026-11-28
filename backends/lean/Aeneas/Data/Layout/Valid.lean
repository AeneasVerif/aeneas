module
public import Aeneas.Data.Layout.Properties

@[expose] public section

namespace Aeneas

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

@[grind =]
def TaggersDisjoint (l : List TagToWrite) : Prop :=
  ∀ n1 n2 (h1 : n1 < l.length) (h2 : n2 < l.length), n1 ≠ n2 →
    disj_range
      (l[n1].offset, l[n1].offset + l[n1].ty.size)
      (l[n2].offset, l[n2].offset + l[n2].ty.size)

structure EnumValid {vs : List MType}
      (variant_tags : (idx : Nat) → idx < vs.length → List TagToWrite)
      (variant_layouts : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (discr : Discriminator)
      (sa : SizeAndAlign) where
  data_sizes : ∀ idx (h : idx < vs.length), (variant_layouts idx h).size = sa.size
  data_aligns : ∀ idx (h : idx < vs.length), (variant_layouts idx h).size_and_align.align ≤ sa.align
  taggers_valid : ∀ idx (h : idx < vs.length), (variant_tags idx h).Forall (·.Valid sa)
  taggers_disjoint : ∀ idx (h : idx < vs.length), TaggersDisjoint (variant_tags idx h)
  discriminator_valid : discr.Valid sa vs.length
  /-- Writing variant `idx`'s tags into the bytes around the data does not clobber any
      initialized byte written by `variant_layouts idx`. -/
  -- this needs extra conditions when we add unions (since then `le_defined` on `Value` stops being equality).
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
  | int ty sa h : Valid (.int sa h : Layout (.int ty))
  | tuple ts f fo fl sa :
      (∀ idx (h : idx < ts.length), (fl idx h).Valid) →
      TupleValid ts.length fo (λ i hi ↦ (fl i hi).size) sa →
      (@Layout.tuple ts f fo fl sa).satisfies →
      Valid (.tuple fo fl sa : Layout (.tuple ts f))
  | enum vs f vt vl dc sa :
      (∀ idx (h : idx < vs.length), (vl idx h).Valid) →
      EnumValid vt vl dc sa →
      (@Layout.enum vs f vt vl dc sa).satisfies →
      Valid (.enum vt vl dc sa : Layout (.enum vs f))

/-! ## Lemmas -/

@[grind →] theorem disj_range_def r1 r2 :
  disj_range r1 r2 → ∀ n, r1.1 ≤ n → n < r1.2 → r2.1 ≤ n → n < r2.2 → False := λ x ↦ x

@[grind →]
lemma Valid.satisfies {ty : MType} {l : Layout ty} (hl : l.Valid) : l.satisfies :=
  match hl with
  | .int _ _ _ => trivial
  | .tuple _ _ _ _ _ _ _ h_sat => h_sat
  | .enum _ _ _ _ _ _ _ _ h_sat => h_sat

/-! ## `ReprC` Validity Lemmas -/

namespace ReprC

@[grind ←]
lemma tupleValid {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat := 0) (h_align : ∀ i (hi : i < n), (falign i hi).isPowerOfTwo) :
    TupleValid n (tupleFieldOffset fsize falign init_off) fsize (tupleSizeAndAlign fsize falign init_off h_align) := by
  grind

@[grind ←]
lemma mkTuple_core_valid (ts : List MType) {f : TupleFlags}
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (max_align : Option { a : Nat // a.isPowerOfTwo } := none)
    (init_off : Nat := 0)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid)
    (h_sat : (mkTuple ts (f := f) fl max_align init_off).satisfies) :
    (mkTuple ts (f := f) fl max_align init_off).Valid :=
  .tuple ts f _ fl _ h_fl (tupleValid _ _ init_off _) h_sat

@[grind ←]
lemma mkTuple_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    (mkTuple ts (f := ⟨.reprC, .reasonablyAligned⟩) fl none 0).Valid := by
  apply mkTuple_core_valid <;> grind

@[grind ←]
lemma mkTuple_packed_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    (mkTuple ts (f := ⟨.reprC, .packed n hn⟩) fl (.some ⟨n, hn⟩) 0).Valid := by
  apply mkTuple_core_valid <;> grind

@[grind ←]
lemma mkTuple_rust_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (init_off : Nat := 0)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    (mkTuple ts (f := ⟨.reprRust, .reasonablyAligned⟩) fl none init_off).Valid := by
  apply mkTuple_core_valid <;> grind

lemma mkTuple_transparent_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (n : Nat)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid)
    (h_zst : ∀ i (hi : i < ts.length), i ≠ n →
      (fl i hi).size_and_align.size = 0 ∧ (fl i hi).size_and_align.align = 1) :
    (mkTuple ts (f := ⟨.reprTransparent, .reasonablyAligned⟩) fl none 0).Valid :=
  mkTuple_core_valid ts fl none 0 h_fl (mkTuple_transparent ts fl n h_zst)

@[grind ←]
lemma mkTuple_rust_packed_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    (mkTuple ts (f := ⟨.reprRust, .packed n hn⟩) fl (.some ⟨n, hn⟩) 0).Valid := by
  apply mkTuple_core_valid <;> grind

@[grind ←]
lemma alignTupleUp_tupleValid {n : Nat} (fo fsize : (idx : Nat) → idx < n → Nat)
    (sa : SizeAndAlign) (a : Nat) (ha : a.isPowerOfTwo)
    (h : TupleValid n fo fsize sa) :
    let na := max sa.align a
    let ns := alignUp sa.size na
    TupleValid n fo fsize ⟨ns, na, by grind, by grind⟩ := by
  grind

lemma mkTuple_aligned_core_valid (ts : List MType) {f : TupleFlags}
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (n : Nat) (hn : n.isPowerOfTwo) (init_off : Nat := 0)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid)
    (h_sat : ((mkTuple ts (f := f) fl none init_off).alignTupleUp n hn).satisfies) :
    ((mkTuple ts (f := f) fl none init_off).alignTupleUp n hn).Valid :=
  .tuple ts f _ fl _ h_fl (alignTupleUp_tupleValid _ _ _ n hn (tupleValid _ _ init_off _)) h_sat

@[grind ←]
lemma mkTuple_aligned_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    ((mkTuple ts (f := ⟨.reprC, .aligned n hn⟩) fl none 0).alignTupleUp n hn).Valid := by
  apply mkTuple_aligned_core_valid <;> grind

@[grind ←]
lemma mkTuple_rust_aligned_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (n : Nat) (hn : n.isPowerOfTwo) (init_off : Nat := 0)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    ((mkTuple ts (f := ⟨.reprRust, .aligned n hn⟩) fl none init_off).alignTupleUp n hn).Valid := by
  apply mkTuple_aligned_core_valid <;> grind

private lemma encode_tuple_prefix_uninit {ts : List MType} {f : TupleFlags}
    (fo : (idx : Nat) → idx < ts.length → Nat)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (v : MVal) (hv : v.valid_for (.tuple ts f)) {j : Nat} (hj : j < sa.size)
    (hoff : ∀ idx (h : idx < ts.length), j < fo idx h) :
    (encode (.tuple fo fl sa : Layout (.tuple ts f)) v hv)[j] = .uninit := by
  cases v with
  | int _ | variant _ _ => nomatch hv
  | tuple values => simp only [encode]; rw [Bytes.foldl_write_subslice_getElem_eq] <;> grind

private lemma padVariantLayout_uninit {t : MType} (ht : t.isTuple) (cl : Layout t)
    (min_off payload_off : Nat) (h_min : TupleMinOffset min_off cl)
    (sa : SizeAndAlign) :
    let vl := padVariantLayout cl payload_off sa
    ∀ (v : MVal) (hv : v.valid_for t) (j : Nat) (hj : j < vl.size),
      j < min_off + payload_off → (encode vl v hv)[j] = .uninit :=
  match t, ht, cl with
  | .int _, h, _ | .enum _ _, h, _ => nomatch h
  | .tuple _ _, _, .tuple _ vfl _ =>
    λ v hv j hj _ ↦ encode_tuple_prefix_uninit _ vfl sa v hv hj (by grind)

@[grind ←]
lemma padVariantLayout_valid {t : MType} (ht : t.isTuple) (cl : Layout t) (hcl : cl.Valid)
    (payload_off : Nat) (sa : SizeAndAlign) (h_size : payload_off + cl.size ≤ sa.size)
    (h_align : cl.size_and_align.align ≤ sa.align) (h_dvd : sa.align ∣ payload_off) :
    (padVariantLayout cl payload_off sa).Valid :=
  match t, ht, cl, hcl with
  | .int _, h, _, _ | .enum _ _, h, _, _ => nomatch h
  | .tuple ts _, .tuple _, .tuple _ vfl _, .tuple _ _ _ _ _ h_vfl_valid h_vtuple h_sat =>
    .tuple ts ⟨.reprRust, .reasonablyAligned⟩ _ vfl sa h_vfl_valid
      ⟨by intro i1 i2 hi1 hi2 hne n
          have := h_vtuple.fields_disj i1 i2 hi1 hi2 hne (n - payload_off)
          grind,
       by grind⟩
      (by simp only [satisfies] at h_sat ⊢
          exact padVariantLayout_reasonablyAligned (.tuple _ vfl _) h_sat payload_off sa h_align h_dvd)

private lemma usize_max_lt_two_pow : Std.Usize.max < 2 ^ (IUScalarTy.unsigned .Usize).numBits := by
  rcases System.Platform.numBits_eq with h | h <;>
    simp [Std.Usize.max, Std.Usize.numBits, IUScalarTy.numBits, Std.UScalarTy.numBits, h]

grind_pattern usize_max_lt_two_pow => Std.Usize.max

lemma mkEnumCore_enumValid (tagTy : IUScalarTy) (shift_payload : Bool)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_min : ∀ idx (h : idx < vs.length), TupleMinOffset (if shift_payload then 0 else tagTy.size) (cl idx h))
    (payload_off : Nat) (sa : SizeAndAlign)
    (hTagBounds : 0 + tagTy.size ≤ sa.size)
    (hTagPayload : tagTy.size ≤ (if shift_payload then 0 else tagTy.size) + payload_off) :
    let vl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx] := λ idx h ↦ padVariantLayout (cl idx h) payload_off sa
    let vt : (idx : Nat) → idx < vs.length → List TagToWrite := λ idx _ ↦ [⟨0, tagTy, IUScalar.fromBv (BitVec.ofNat tagTy.numBits idx)⟩]
    let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
    EnumValid vt vl discr sa := by
  intro vl vt discr
  have h_pad := λ (idx : Nat) (h : idx < vs.length) ↦
    padVariantLayout_uninit (ht idx h) (cl idx h)
      (if shift_payload then 0 else tagTy.size) payload_off (h_min idx h) sa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · grind [List.Forall]
  · grind
  · grind
  -- 1. `tags_preserve_payload`: tag writes into `[0 ..< tagTy.size) ⊆ [0 ..< min_off + payload_off)`, which is `.uninit`.
  · intro idx h_idx v hv payload_bs k hk
    have := h_pad idx h_idx v hv k (by simp [hk])
    simp [encode_discriminant, vt, payload_bs, vl, hk]
    grind
  -- 2. `discr_complete`: reading `tagTy` back from `[0 ..< tagTy.size)` recovers `idx`.
  · intro idx h_idx v hv
    unfold decode_discriminant
    simp [encode_discriminant, vt, Nat.mod_eq_of_lt (by omega : idx < 2 ^ tagTy.numBits), h_idx]
    grind
  -- 3. `discr_tags_le_defined`: if `decode_discriminant bytes discr = some idx`, `bytes[0 ..< tagTy.size)` matches `vt idx`.
  · intro bytes idx h_idx h_dec
    simp only [discr, decode_discriminant, hTagBounds, ↓reduceDIte] at h_dec
    cases h_data : (bytes.subslice_with_length 0 tagTy.size hTagBounds).toData with
    | none => simp [h_data] at h_dec
    | some bytes_data =>
      simp [h_data, apply_ite (decode_discriminant bytes)] at h_dec
      have : Endianness.encode_bitvec tagTy.size (BitVec.ofNat tagTy.numBits idx) = bytes_data := by
        simp [← h_dec.2]
      intro k hk
      simp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv_fromBv]
      grind

lemma mkEnumCore_valid (tagTy : IUScalarTy) (shift_payload : Bool)
    (vs : List MType) {f : EnumFlags} (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (h_min : ∀ idx (h : idx < vs.length), TupleMinOffset (if shift_payload then 0 else tagTy.size) (cl idx h))
    (h_sat : (mkEnumCore tagTy shift_payload vs (f := f) cl).satisfies) :
    (mkEnumCore tagTy shift_payload vs (f := f) cl).Valid :=
  .enum vs f _ _ _ _
    (λ idx h ↦ padVariantLayout_valid (ht idx h) (cl idx h) (h_cl idx h) _ _ (by grind) (by grind) (by grind [Nat.dvd_zero]))
    (mkEnumCore_enumValid tagTy shift_payload vs h_max ht cl h_min _ _ (by grind) (by grind))
    h_sat

private lemma padVariantLayout_alignUp_valid {t : MType} (ht : t.isTuple) (cl : Layout t) (hcl : cl.Valid)
    (payload_off : Nat) (sa sa' : SizeAndAlign) (n : Nat) (hn : n.isPowerOfTwo)
    (h_sa' : sa' = ⟨alignUp sa.size (max sa.align n), max sa.align n, by grind, by grind⟩)
    (h_size : payload_off + cl.size ≤ sa.size)
    (h_align : cl.size_and_align.align ≤ sa.align) (h_dvd : sa.align ∣ payload_off) :
    (padVariantLayout cl payload_off sa').Valid :=
  match t, ht, cl with
  | .tuple ts _, .tuple _, .tuple fo vfl vsa => by
    subst h_sa'
    have h_pad := padVariantLayout_valid (.tuple ts) (.tuple fo vfl vsa) hcl payload_off sa h_size h_align h_dvd
    cases h_pad with
    | tuple _ _ _ _ _ h_fl h_tup h_sat =>
      exact .tuple ts ⟨.reprRust, .reasonablyAligned⟩ _ vfl _ h_fl
        (alignTupleUp_tupleValid _ _ sa n hn h_tup)
        (alignTupleUp_reasonablyAligned (.tuple _ vfl sa) n hn h_sat)

private lemma alignEnumUp_padVariantLayout_aux {t : MType} (ht : t.isTuple) (cl : Layout t)
    (payload_off : Nat) (sa sa' : SizeAndAlign) (n : Nat) (hn : n.isPowerOfTwo)
    (h_sa' : sa' = ⟨alignUp sa.size (max sa.align n), max sa.align n, by grind, by grind⟩) :
    (match t, padVariantLayout cl payload_off sa with
     | .tuple _ _, x => x.alignTupleUp n hn
     | _, x => x) =
    padVariantLayout cl payload_off sa' :=
  match t, ht, cl with
  | .tuple _ _, .tuple _, .tuple _ _ _ => by subst h_sa'; rfl

private lemma alignEnumUp_padVariantLayout {vs : List MType} {f : EnumFlags}
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (vt : (idx : Nat) → idx < vs.length → List TagToWrite)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (payload_off : Nat) (discr : Discriminator) (sa : SizeAndAlign)
    (n : Nat) (hn : n.isPowerOfTwo) :
    (Layout.enum (f := f) vt (λ idx h ↦ padVariantLayout (cl idx h) payload_off sa) discr sa).alignEnumUp n hn =
    let na := max sa.align n
    let ns := alignUp sa.size na
    let sa' : SizeAndAlign := ⟨ns, na, by grind, by grind⟩
    Layout.enum (f := f) vt (λ idx h ↦ padVariantLayout (cl idx h) payload_off sa') discr sa' := by
  simp only [alignEnumUp]
  congr
  funext i hi
  exact alignEnumUp_padVariantLayout_aux (ht i hi) (cl i hi) payload_off sa _ n hn rfl

lemma mkEnumCore_aligned_valid (tagTy : IUScalarTy) (shift_payload : Bool)
    (vs : List MType) {f : EnumFlags} (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (h_min : ∀ idx (h : idx < vs.length), TupleMinOffset (if shift_payload then 0 else tagTy.size) (cl idx h))
    (h_sat : ((mkEnumCore tagTy shift_payload vs (f := f) cl).alignEnumUp n hn).satisfies) :
    ((mkEnumCore tagTy shift_payload vs (f := f) cl).alignEnumUp n hn).Valid := by
  revert h_sat
  unfold mkEnumCore
  rw [alignEnumUp_padVariantLayout ht]
  intro h_sat
  exact .enum vs f _ _ _ _
    (λ idx h ↦ padVariantLayout_alignUp_valid (ht idx h) (cl idx h) (h_cl idx h) _ _ _ n hn rfl (by grind) (by grind) (by grind [Nat.dvd_zero]))
    (mkEnumCore_enumValid tagTy shift_payload vs h_max ht cl h_min _ _ (by grind) (by grind))
    h_sat

@[grind ←]
lemma mkEnum_valid (vs : List MType) (h_max : vs.length ≤ 2 ^ (IUScalarTy.unsigned .Usize).numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (hcl_reprC : ∀ idx (h : idx < vs.length), IsReprCTuple 0 .reasonablyAligned (cl idx h)) :
    (mkEnum (.unsigned .Usize) vs (f := ⟨.reprC, .reasonablyAligned⟩) cl).Valid := by
  apply mkEnumCore_valid <;> grind

@[grind ←]
lemma mkEnum_prim_valid (tagTy : IUScalarTy)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (hcl_reprC : ∀ idx (h : idx < vs.length), IsReprCTuple 0 .reasonablyAligned (cl idx h)) :
    (mkEnum tagTy vs (f := ⟨.reprC_prim tagTy, .reasonablyAligned⟩) cl).Valid := by
  apply mkEnumCore_valid <;> grind

@[grind ←]
lemma mkEnum_rust_valid (tagTy : IUScalarTy := .unsigned .Usize)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid) :
    (mkEnum tagTy vs (f := ⟨.reprRust, .reasonablyAligned⟩) cl).Valid := by
  apply mkEnumCore_valid <;> grind

@[grind ←]
lemma mkEnumPrimitive_valid (tagTy : IUScalarTy)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (hcl_reprC : ∀ idx (h : idx < vs.length), IsReprCTuple tagTy.size .reasonablyAligned (cl idx h)) :
    (mkEnumPrimitive tagTy vs (f := ⟨.reprPrim tagTy, .reasonablyAligned⟩) cl).Valid := by
  apply mkEnumCore_valid <;> grind

@[grind ←]
lemma mkEnumPrimitive_rust_valid (tagTy : IUScalarTy)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (h_min : ∀ idx (h : idx < vs.length), TupleMinOffset tagTy.size (cl idx h)) :
    (mkEnumPrimitive tagTy vs (f := ⟨.reprRust, .reasonablyAligned⟩) cl).Valid := by
  apply mkEnumCore_valid <;> grind

@[grind ←]
lemma mkEnum_aligned_valid (vs : List MType) (h_max : vs.length ≤ 2 ^ (IUScalarTy.unsigned .Usize).numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (hcl_reprC : ∀ idx (h : idx < vs.length), IsReprCTuple 0 .reasonablyAligned (cl idx h)) :
    ((mkEnum (.unsigned .Usize) vs (f := ⟨.reprC, .aligned n hn⟩) cl).alignEnumUp n hn).Valid := by
  apply mkEnumCore_aligned_valid <;> grind

@[grind ←]
lemma mkEnum_prim_aligned_valid (tagTy : IUScalarTy)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (hcl_reprC : ∀ idx (h : idx < vs.length), IsReprCTuple 0 .reasonablyAligned (cl idx h)) :
    ((mkEnum tagTy vs (f := ⟨.reprC_prim tagTy, .aligned n hn⟩) cl).alignEnumUp n hn).Valid := by
  apply mkEnumCore_aligned_valid <;> grind

@[grind ←]
lemma mkEnum_rust_aligned_valid (tagTy : IUScalarTy := .unsigned .Usize)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid) :
    ((mkEnum tagTy vs (f := ⟨.reprRust, .aligned n hn⟩) cl).alignEnumUp n hn).Valid := by
  apply mkEnumCore_aligned_valid <;> grind

@[grind ←]
lemma mkEnumPrimitive_aligned_valid (tagTy : IUScalarTy)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (hcl_reprC : ∀ idx (h : idx < vs.length), IsReprCTuple tagTy.size .reasonablyAligned (cl idx h)) :
    ((mkEnumPrimitive tagTy vs (f := ⟨.reprPrim tagTy, .aligned n hn⟩) cl).alignEnumUp n hn).Valid := by
  apply mkEnumCore_aligned_valid <;> grind

@[grind ←]
lemma mkEnumPrimitive_rust_aligned_valid (tagTy : IUScalarTy)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (n : Nat) (hn : n.isPowerOfTwo)
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (h_min : ∀ idx (h : idx < vs.length), TupleMinOffset tagTy.size (cl idx h)) :
    ((mkEnumPrimitive tagTy vs (f := ⟨.reprRust, .aligned n hn⟩) cl).alignEnumUp n hn).Valid := by
  apply mkEnumCore_aligned_valid <;> grind

end ReprC
end Layout
end Aeneas
