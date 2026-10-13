module
public import Aeneas.Data.Layout.Defs
public section

namespace Aeneas

/-! ## Helper Lemmas for `Endianness` and Discriminants -/

namespace Endianness

@[simp, grind =]
lemma decode_bitvec_encode_bitvec (ty : IUScalarTy) (bv : BitVec ty.numBits) :
    decode_bitvec ty (encode_bitvec ty.size bv) = bv := by
  ext k hk
  simp only [decode_bitvec, BitVec.getElem_ofFn, encode_bitvec, Vector.getElem_ofFn, BitVec.getElem_extractLsb']
  change bv.getLsbD (8 * (k / 8) + k % 8) = bv.getLsbD k
  congr 1; omega

@[simp, grind =]
lemma encode_bitvec_decode_bitvec (ty : IUScalarTy) (bytes_data : Vector Byte ty.size) :
    encode_bitvec ty.size (decode_bitvec ty bytes_data) = bytes_data := by
  ext i hi r hr
  have hbit : 8 * i + r < ty.numBits := by have := mul_8_size_eq (ty := ty); omega
  simp only [encode_bitvec, Vector.getElem_ofFn, BitVec.getElem_extractLsb']
  change (decode_bitvec ty bytes_data)[8 * i + r] = bytes_data[i][r]
  simp [IUScalarTy.size, decode_bitvec, show (8 * i + r) / 8 = i by omega, show (8 * i + r) % 8 = r by omega]; trivial

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

lemma encode_decode (ty : IUScalarTy) (bytes_data : Vector Byte ty.size) :
    encode ty (decode ty bytes_data) (decode_can_repr ty bytes_data) = bytes_data := by
  cases ty with
  | unsigned u =>
    simp only [encode, decode, IUScalarTy.numBits, Int.toNat_natCast, BitVec.ofNat_toNat,
               BitVec.setWidth_eq, encode_bitvec_decode_bitvec]
  | signed st =>
    simp only [encode, decode, BitVec.ofInt_toInt, encode_bitvec_decode_bitvec]

end Endianness

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
        have h_sub_eq := Bytes.eq_of_toData_some_le_defined h_data (by apply Bytes.subslice_le_defined; trivial)
        rw [← h_sub_eq, h_data]
        apply decode_discriminant_mono; trivial

lemma encode_discriminant_le_defined {n : Nat} (payload bytes : Bytes n) (tags : List TagToWrite)
    (h_pay : payload.le_defined bytes)
    (h_tag : (encode_discriminant (Bytes.uninit n) tags).le_defined bytes) :
    (encode_discriminant payload tags).le_defined bytes :=
  Bytes.foldl_write_subslice_overlay_le_defined tags (·.offset)
    (λ tag ↦ (Endianness.encode_bitvec tag.ty.size tag.data.bv).map .init)
    payload bytes h_pay h_tag

namespace Layout

@[grind →] theorem disj_range_def r1 r2 :
  disj_range r1 r2 → ∀ n, r1.1 ≤ n → n < r1.2 → r2.1 ≤ n → n < r2.2 → False := λ x ↦ x

/-! ## Helper Lemmas for Proving the Galois Connection Properties -/

private lemma list_mapM_mono {α β : Type} {f1 f2 : α → Option β} (xs : List α)
    (hf : ∀ x ∈ xs, Option.le_defined (f1 x) (f2 x)) :
    Option.le_defined (xs.mapM f1) (xs.mapM f2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons]
    apply Option.le_defined.bind; grind
    intros α hα
    apply Option.le_defined.bind; grind
    intros _ _; rfl

@[simp, grind →] private lemma list_mapM_eq_some_length {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], _, h => by grind
  | x :: xs, _, h => by
    simp [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, zs, hzs, rfl⟩ := h
    simp [list_mapM_eq_some_length hzs]

@[grind →] private lemma list_mapM_eq_some_getElem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β} (h : xs.mapM f = some ys) (i : Nat) (hi : i < xs.length),
      f xs[i] = some (ys[i]'(by grind))
  | x :: xs, _, h, 0, _ => by
    simp [Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, zs, _, rfl⟩ := h; exact hy
  | x :: xs, _, h, i + 1, hi => by
    simp [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, zs, hzs, rfl⟩ := h
    exact list_mapM_eq_some_getElem hzs i (Nat.lt_of_succ_lt_succ hi)

@[grind ←] private lemma list_mapM_eq_some_of_getElem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β} (h_len : ys.length = xs.length),
      (∀ (i : Nat) (hi : i < xs.length), f xs[i] = some (ys[i]'(by grind))) →
      xs.mapM f = some ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, h_len, h_get => by
    have h0 : f x = some y := h_get 0 (by grind)
    have ih := list_mapM_eq_some_of_getElem (by grind) (λ i hi ↦ h_get (i + 1) (by grind))
    simp [h0, ih]

private lemma list_mapM_finRange_eq_some {α : Type} {n : Nat} {f : Fin n → Option α} {ys : List α}
    (h : (List.finRange n).mapM f = some ys) (idx : Fin n) :
    f idx = some (ys[idx.val]'(by grind)) := by
  -- this proof is a bit silly, why does grind not see this by itself?
  have _ : f idx = f (List.finRange n)[↑idx] := by grind
  grind

private lemma list_mapM_finRange_of_getElem {α : Type} {n : Nat} {f : Fin n → Option α} {ys : List α}
    (h_len : ys.length = n)
    (h_get : ∀ (idx : Fin n), f idx = some (ys[idx.val]'(by grind))) :
    (List.finRange n).mapM f = some ys := by grind

private lemma encode_tuple_subslice {ts : List MType} (fo : Fin ts.length → Nat)
    (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (h_tuple : TupleValid fo (λ i ↦ (fl i).size) sa)
    (values : List MVal) (hv : (MVal.tuple values).valid_for (.tuple ts))
    (idx : Fin ts.length) :
    let i : Fin values.length := ⟨idx.val, by grind⟩
    (encode (.tuple fo fl sa) (.tuple values) hv).subslice_with_length
      (fo idx) (fl idx).size (h_tuple.size_bounds idx) =
    encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i) :=
  Bytes.foldl_write_subslice_nodup_subslice _ _ _ _ idx
    (List.mem_finRange idx) (List.nodup_finRange ts.length) (h_tuple.size_bounds idx)
    (λ y _ ↦ h_tuple.fields_disj idx y)

private lemma encode_tuple_le_defined {ts : List MType} (fo : Fin ts.length → Nat)
    (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (bytes : Bytes sa.size) (values : List MVal) (hv : (MVal.tuple values).valid_for (.tuple ts))
    (h_bounds : ∀ idx : Fin ts.length, fo idx + (fl idx).size ≤ sa.size)
    (h_fields : ∀ idx : Fin ts.length,
      let i : Fin values.length := ⟨idx.val, by grind⟩
      (encode (fl idx) values[i] (by grind)).le_defined
        (bytes.subslice_with_length (fo idx) (fl idx).size (h_bounds idx))) :
    (encode (.tuple fo fl sa) (.tuple values) hv).le_defined bytes := by
  apply Bytes.foldl_write_subslice_le_defined <;> grind

/-! ## Proofs of the Four Generic Representation Properties -/

theorem valid_decodeValid {ty : MType} (l : Layout ty) (hl : l.Valid) : l.DecodeValid := by
  induction hl with
  | int st =>
    intro bytes val h_dec
    simp only [decode, Option.bind_eq_bind] at h_dec
    cases h_data : bytes.toData with
    | none => grind
    | some bytes_data =>
      have := MVal.valid_for.int (Endianness.decode_can_repr st bytes_data)
      grind
  | tuple ts fo fl sa _ _ ih =>
    intro bytes val h_dec
    simp [decode] at h_dec
    obtain ⟨values, h_mapM, rfl⟩ := h_dec
    apply MVal.valid_for.tuple
    apply List.forall₂_iff_get.mpr ⟨by grind, λ i hi1 hi2 ↦ ?_⟩
    have h_item := list_mapM_finRange_eq_some h_mapM ⟨i, hi2⟩
    split at h_item
    case isFalse => nomatch h_item
    case isTrue h_bound =>
      exact ih ⟨i, hi2⟩ _ _ h_item
  | enum vs vt vl dc sa _ _ ih =>
    intro bytes val h_dec
    simp only [decode, Option.bind_eq_bind] at h_dec
    cases h_discr : decode_discriminant bytes dc with
    | none => simp [h_discr] at h_dec
    | some d =>
      simp only [h_discr, Option.bind_some] at h_dec
      split at h_dec
      case isFalse => nomatch h_dec
      case isTrue hd =>
        split at h_dec
        case isFalse => nomatch h_dec
        case isTrue hsz =>
          cases h_vdec : decode (vl ⟨d, hd⟩) (bytes.subslice_with_length 0 _ hsz) with
          | none => simp [h_vdec] at h_dec
          | some v =>
            have := MVal.valid_for.enum d v vs hd (ih ⟨d, hd⟩ _ _ h_vdec)
            grind

/-- Combines `decode` with a `DecodeValid` proof to return a subtype `{ val : MVal // val.valid_for ty }`. -/
def Valid.decode {ty : MType} {l : Layout ty} (hl : l.Valid)
    (bytes : Bytes l.size) : Option { val : MVal // val.valid_for ty } :=
  match h : Layout.decode l bytes with
  | none => none
  | some val => some ⟨val, valid_decodeValid _ hl _ _ h⟩

theorem valid_decodeMono {ty : MType} (l : Layout ty) (hl : l.Valid) : l.DecodeMono := by
  induction hl with
  | int st =>
    intro bytes1 bytes2 h_le
    simp only [decode, Option.bind_eq_bind]
    cases h_data1 : bytes1.toData with
    | none => simp
    | some data1 =>
      rw [← Bytes.eq_of_toData_some_le_defined h_data1 h_le, h_data1]; simp
  | tuple ts fo fl sa _ _ ih =>
    intro bytes1 bytes2 h_le
    apply Option.le_defined.map
    refine list_mapM_mono (List.finRange ts.length) λ idx _ ↦ ?_
    dsimp only; split
    case isFalse => trivial
    case isTrue h_bound =>
      apply ih
      all_goals grind
  | enum vs vt vl dc sa _ _ ih =>
    intro bytes1 bytes2 h_le
    simp only [decode]
    apply Option.le_defined.bind
    { grind }
    intros d _
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
    | tuple _ | variant _ _ => nomatch hv
    | int i => simp [encode, decode, Endianness.decode_encode st i hv.int_can_repr]
  | tuple ts fo fl sa _ h_tuple ih =>
    intro val hv
    cases val with
    | int _ | variant _ _ => nomatch hv
    | tuple values =>
      simp only [decode]
      rw [list_mapM_finRange_of_getElem hv.tuple_len]
      · rfl
      · intro idx
        simp only [h_tuple.size_bounds idx, ↓reduceDIte, encode_tuple_subslice fo fl sa h_tuple values hv idx]
        apply ih
  | enum vs vt vl dc sa h_vl_valid h_enum ih =>
    intro val hv
    cases val with
    | int _ | tuple _ => nomatch hv
    | variant d data =>
      let idx : Fin vs.length := ⟨d, hv.variant_bound⟩
      have hsz : 0 + (vl idx).size ≤ sa.size := by have := h_enum.data_sizes idx; grind
      simp only [encode, decode, Option.bind_eq_bind]
      rw [h_enum.discr_complete idx data hv.variant_proj]
      simp only [Option.bind_some, idx.isLt, hsz, ↓reduceDIte]
      have h_le_sub := Bytes.subslice_le_defined (h_enum.tags_preserve_payload idx data hv.variant_proj) 0 _ hsz
      have h_mono := valid_decodeMono (vl idx) (h_vl_valid idx) _ _ h_le_sub
      simp only [Bytes.subslice_write_subslice_self, ih idx data hv.variant_proj,
                 Option.le_defined.eq_of_some] at h_mono
      rw [h_mono]; rfl

theorem valid_encodeDecodeLeDefined {ty : MType} (l : Layout ty) (hl : l.Valid) : l.EncodeDecodeLeDefined := by
  induction hl with
  | int st =>
    intro bytes val hv h_dec
    cases val with
    | tuple _ | variant _ _ => nomatch hv
    | int i =>
      simp only [decode, Option.bind_eq_bind] at h_dec
      cases h_data : bytes.toData with
      | none => rw [h_data] at h_dec; nomatch h_dec
      | some bytes_data =>
        rw [h_data] at h_dec; simp at h_dec; subst h_dec
        have h_eq : encode .int (.int (Endianness.decode st bytes_data)) hv = bytes := by
          ext k hk
          simp [encode, Endianness.encode_decode st bytes_data]
          exact (Bytes.getElem_of_toData h_data k hk).symm
        simp [h_eq]
  | tuple ts fo fl sa _ h_tuple ih =>
    intro bytes val hv h_dec
    cases val with
    | int _ | variant _ _ => nomatch hv
    | tuple values =>
      simp only [decode, Option.map_eq_some_iff] at h_dec
      obtain ⟨dec_values, h_mapM, h_eq⟩ := h_dec
      injection h_eq with h_eq; subst h_eq
      apply encode_tuple_le_defined fo fl sa bytes dec_values hv h_tuple.size_bounds
      intro idx
      have h_item := list_mapM_finRange_eq_some h_mapM idx
      simp [h_tuple.size_bounds idx] at h_item
      exact ih idx _ _ _ h_item
  | enum vs vt vl dc sa _ h_enum ih =>
    intro bytes val hv h_dec
    cases val with
    | int _ | tuple _ => nomatch hv
    | variant d data =>
      simp only [decode, Option.bind_eq_bind] at h_dec
      cases h_discr : decode_discriminant bytes dc with
      | none => simp [h_discr] at h_dec
      | some d_dec =>
        simp only [h_discr, Option.bind_some] at h_dec
        split at h_dec
        case isFalse => nomatch h_dec
        case isTrue hd =>
          split at h_dec
          case isFalse => nomatch h_dec
          case isTrue hsz =>
            cases h_vdec : decode (vl ⟨d_dec, hd⟩) (bytes.subslice_with_length 0 _ hsz) with
            | none => simp [h_vdec] at h_dec
            | some v_dec =>
              simp [h_vdec] at h_dec
              obtain ⟨rfl, rfl⟩ := h_dec
              let idx : Fin vs.length := ⟨d_dec, hd⟩
              let payload_bs := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (vl idx) v_dec hv.variant_proj)
              have h_pay_le : payload_bs.le_defined bytes := λ k ↦ by
                have h_ksz : k.val < (vl idx).size := by have := h_enum.data_sizes idx; grind
                have hf := ih idx _ v_dec hv.variant_proj h_vdec ⟨k.val, h_ksz⟩
                simpa [payload_bs, Bytes.subslice_with_length, h_ksz] using hf
              exact encode_discriminant_le_defined payload_bs bytes (vt idx) h_pay_le
                (h_enum.discr_tags_le_defined bytes idx h_discr)

end Layout

end Aeneas

