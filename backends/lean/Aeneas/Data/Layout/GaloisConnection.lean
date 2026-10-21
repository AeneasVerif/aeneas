module
public import Aeneas.Data.Layout.Valid
public section

namespace Aeneas
namespace Layout

/-! ## Helper Lemmas for Proving the Galois Connection Properties -/

@[grind ←] private lemma list_mapM_mono {α β : Type} {f1 f2 : α → Option β} (xs : List α)
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

@[grind →] private lemma list_mapM_range_attach_eq_some {α : Type} {n : Nat}
    {f : { x // x ∈ List.range n } → Option α} {ys : List α}
    (h : (List.range n).attach.mapM f = some ys) (idx : Nat) (h_idx : idx < n) :
    f ⟨idx, List.mem_range.mpr h_idx⟩ = some (ys[idx]'(by grind)) := by
  have _ : f ⟨idx, List.mem_range.mpr h_idx⟩ = f ((List.range n).attach[idx]'(by grind)) := by grind
  grind

@[grind ←] private lemma list_mapM_range_attach_of_getElem {α : Type} {n : Nat}
    {f : { x // x ∈ List.range n } → Option α} {ys : List α}
    (h_len : ys.length = n)
    (h_get : ∀ (idx : Nat) (h_idx : idx < n),
      f ⟨idx, List.mem_range.mpr h_idx⟩ = some (ys[idx]'(by grind))) :
    (List.range n).attach.mapM f = some ys := by grind

@[simp] private lemma encode_tuple_subslice {ts : List MType} {f : TupleFlags}
    (fo : (idx : Nat) → idx < ts.length → Nat)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (values : List MVal) (hv : (MVal.tuple values).valid_for (.tuple ts f))
    (idx : Nat) (h_idx : idx < ts.length)
    (h_bound : fo idx h_idx + (fl idx h_idx).size ≤ sa.size)
    (h_disj : ∀ (i1 i2 : Nat) (hi1 : i1 < ts.length) (hi2 : i2 < ts.length), i1 ≠ i2 →
      disj_range (fo i1 hi1, fo i1 hi1 + (fl i1 hi1).size)
                 (fo i2 hi2, fo i2 hi2 + (fl i2 hi2).size)) :
    (encode (.tuple fo fl sa : Layout (.tuple ts f)) (.tuple values) hv).subslice_with_length
      (fo idx h_idx) (fl idx h_idx).size h_bound =
    encode (fl idx h_idx) (values[idx]'(by grind)) (by grind) :=
  Bytes.foldl_write_subslice_nodup_subslice (List.range ts.length).attach
    (λ x ↦ fo x.val (by grind))
    (λ x ↦ encode (fl x.val (by grind)) (values[x.val]'(by grind)) (by grind))
    (Bytes.uninit sa.size) ⟨idx, List.mem_range.mpr h_idx⟩
    (List.mem_attach _ _) (List.nodup_attach.mpr List.nodup_range)
    h_bound (by grind)

grind_pattern encode_tuple_subslice =>
  (encode (.tuple fo fl sa : Layout (.tuple ts f)) (.tuple values) hv).subslice_with_length (fo idx h_idx) (fl idx h_idx).size h_bound,
  values[idx]

@[grind ←] private lemma encode_tuple_le_defined {ts : List MType} {f : TupleFlags}
    (fo : (idx : Nat) → idx < ts.length → Nat)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (bytes : Bytes sa.size) (values : List MVal) (hv : (MVal.tuple values).valid_for (.tuple ts f))
    (h_bounds : ∀ idx (h_idx : idx < ts.length), fo idx h_idx + (fl idx h_idx).size ≤ sa.size)
    (h_fields : ∀ idx (h_idx : idx < ts.length),
      (encode (fl idx h_idx) (values[idx]'(by grind)) (by grind)).le_defined
        (bytes.subslice_with_length (fo idx h_idx) (fl idx h_idx).size (h_bounds idx h_idx))) :
    (encode (.tuple fo fl sa : Layout (.tuple ts f)) (.tuple values) hv).le_defined bytes := by
  apply Bytes.foldl_write_subslice_le_defined <;> grind

/-! ## Proofs of the Four Generic Representation Properties -/

theorem valid_decodeValid {ty : MType} (l : Layout ty) (hl : l.Valid) : l.DecodeValid := by
  induction hl with
  | int st sa hs =>
    rcases sa with ⟨sz, align, wf_align, wf_size⟩; dsimp only [SizeAndAlign.ValidForScalar] at hs; subst hs
    intro bytes val h_dec
    simp only [decode, Option.bind_eq_bind] at h_dec
    cases h_data : bytes.toData <;> grind
  | tuple ts f fo fl sa _ _ _ ih =>
    intro bytes val h_dec
    simp [decode] at h_dec
    obtain ⟨values, h_mapM, rfl⟩ := h_dec
    apply MVal.valid_for.tuple
    apply List.forall₂_iff_get.mpr ⟨by grind, λ i hi1 hi2 ↦ ?_⟩
    have h_item := list_mapM_range_attach_eq_some h_mapM i hi2
    split at h_item
    case isFalse => nomatch h_item
    case isTrue h_bound => exact ih i hi2 _ _ h_item
  | enum vs f vt vl dc sa _ _ _ ih =>
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
          cases h_vdec : decode (vl d hd) (bytes.subslice_with_length 0 _ hsz) with
          | none => simp [h_vdec] at h_dec
          | some v =>
            have := ih d hd _ _ h_vdec
            simp [h_vdec] at h_dec
            grind

/-- Combines `decode` with a `DecodeValid` proof to return a subtype `{ val : MVal // val.valid_for ty }`. -/
def Valid.decode {ty : MType} {l : Layout ty} (hl : l.Valid)
    (bytes : Bytes l.size) : Option { val : MVal // val.valid_for ty } :=
  match h : Layout.decode l bytes with
  | none => none
  | some val => some ⟨val, valid_decodeValid _ hl _ _ h⟩

theorem valid_decodeMono {ty : MType} (l : Layout ty) (hl : l.Valid) : l.DecodeMono := by
  induction hl with
  | int st sa hs =>
    rcases sa with ⟨sz, align, wf_align, wf_size⟩; dsimp only [SizeAndAlign.ValidForScalar] at hs; subst hs
    intro bytes1 bytes2 h_le
    simp only [decode, Option.bind_eq_bind]
    cases h_data1 : bytes1.toData <;> grind
  | tuple ts f fo fl sa _ _ _ ih =>
    intro bytes1 bytes2 h_le
    apply Option.le_defined.map
    refine list_mapM_mono _ λ idx _ ↦ ?_
    dsimp only; split <;> grind
  | enum vs f vt vl dc sa _ _ _ ih =>
    intro bytes1 bytes2 h_le
    simp only [decode]
    apply Option.le_defined.bind; grind
    intros d _
    split
    case isFalse => trivial
    case isTrue hd =>
      split
      case isFalse => trivial
      case isTrue hsz =>
        apply Option.le_defined.bind <;> grind

theorem valid_decodeEncode {ty : MType} (l : Layout ty) (hl : l.Valid) : l.DecodeEncode := by
  induction hl with
  | int st sa hs =>
    rcases sa with ⟨sz, align, wf_align, wf_size⟩; dsimp only [SizeAndAlign.ValidForScalar] at hs; subst hs
    intro val hv
    cases val with
    | tuple _ | variant _ _ => nomatch hv
    | int i => grind [encode, decode]
  | tuple ts f fo fl sa _ h_tuple _ ih =>
    intro val hv
    cases val with
    | int _ | variant _ _ => nomatch hv
    | tuple values =>
      simp only [decode]
      rw [list_mapM_range_attach_of_getElem (ys := values) (by grind)]
      · rfl
      · intro idx h_idx
        rw [dif_pos (h_tuple.size_bounds idx h_idx), encode_tuple_subslice]
        all_goals grind
  | enum vs f vt vl dc sa h_vl_valid h_enum _ ih =>
    intro val hv
    cases val with
    | int _ | tuple _ => nomatch hv
    | variant d data =>
      have hd : d < vs.length := by grind
      have hsz : 0 + (vl d hd).size ≤ sa.size := by have := h_enum.data_sizes d hd; grind
      simp only [encode, decode, Option.bind_eq_bind]
      rw [h_enum.discr_complete d hd data (by grind)]
      simp only [Option.bind_some, hd, hsz, ↓reduceDIte]
      have h_mono := valid_decodeMono (vl d hd) (h_vl_valid d hd) _ _
        (Bytes.subslice_le_defined (h_enum.tags_preserve_payload d hd data (by grind)) 0 _ hsz)
      grind

theorem valid_encodeDecodeLeDefined {ty : MType} (l : Layout ty) (hl : l.Valid) : l.EncodeDecodeLeDefined := by
  induction hl with
  | int st sa hs =>
    rcases sa with ⟨sz, align, wf_align, wf_size⟩; dsimp only [SizeAndAlign.ValidForScalar] at hs; subst hs
    intro bytes val hv h_dec
    cases val with
    | tuple _ | variant _ _ => nomatch hv
    | int i =>
      simp only [decode, Option.bind_eq_bind] at h_dec
      cases h_data : bytes.toData with
      | none => grind
      | some bytes_data =>
        rw [h_data] at h_dec; simp at h_dec; subst h_dec
        have h_eq : encode (.int ⟨_, align, wf_align, wf_size⟩ rfl) (.int (Endianness.decode st bytes_data)) hv = bytes := by
          ext k hk; grind [encode]
        grind
  | tuple ts f fo fl sa _ h_tuple _ ih =>
    intro bytes val hv h_dec
    cases val with
    | int _ | variant _ _ => nomatch hv
    | tuple values =>
      simp only [decode, Option.map_eq_some_iff] at h_dec
      obtain ⟨dec_values, h_mapM, h_eq⟩ := h_dec
      injection h_eq with h_eq; subst h_eq
      apply encode_tuple_le_defined <;> grind
  | enum vs f vt vl dc sa _ h_enum _ ih =>
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
            cases h_vdec : decode (vl d_dec hd) (bytes.subslice_with_length 0 _ hsz) with
            | none => simp [h_vdec] at h_dec
            | some v_dec =>
              simp [h_vdec] at h_dec
              obtain ⟨rfl, rfl⟩ := h_dec
              let payload_bs := (Bytes.uninit sa.size).write_subslice_at_index 0 (encode (vl d_dec hd) v_dec (by grind))
              have h_pay_le : payload_bs.le_defined bytes := λ k hk ↦ by
                have h_ksz : k < (vl d_dec hd).size := by have := h_enum.data_sizes d_dec hd; grind
                have hf := ih d_dec hd _ v_dec (by grind) h_vdec k h_ksz
                grind
              have := h_enum.discr_tags_le_defined bytes d_dec hd h_discr
              grind [encode]

end Layout
end Aeneas
