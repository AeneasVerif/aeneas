module
public import Aeneas.Data.Layout.ReprC

@[expose] public section

namespace Aeneas
namespace Layout

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
  | int ty sa h : ReasonablyAligned (.int sa h : Layout (.int ty))
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

@[grind ←]
lemma alignTupleUp_reasonablyAligned {ts f} (l : Layout (.tuple ts f)) (a : Nat) (ha : a.isPowerOfTwo)
    (h : l.ReasonablyAligned) : (l.alignTupleUp a ha).ReasonablyAligned :=
  match ts, l, h with
  | ts, .tuple fo fl sa, .tuple _ _ _ _ _ h_tup =>
    .tuple ts f fo fl _ ⟨by grind, h_tup.offs_aligned⟩

@[grind ←]
lemma alignEnumUp_reasonablyAligned {vs f} (l : Layout (.enum vs f)) (a : Nat) (ha : a.isPowerOfTwo)
    (h : l.ReasonablyAligned) :
    (l.alignEnumUp a ha).ReasonablyAligned :=
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
lemma alignEnumUp_aligned {vs f} (l : Layout (.enum vs f)) (a : Nat) (ha : a.isPowerOfTwo) :
    (l.alignEnumUp a ha).Aligned a :=
  match vs, l with
  | _, .enum _ _ _ _ => ⟨ha, by simp [alignEnumUp, size_and_align]⟩

/-! ## `ReprC` Layout Properties -/

namespace ReprC

@[grind ←]
lemma mkTuple_reasonablyAligned (ts : List MType) {f : TupleFlags}
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (init_off : Nat := 0) :
    (mkTuple ts (f := f) fl none init_off).ReasonablyAligned :=
  .tuple ts f _ fl _ (by grind)

grind_pattern mkTuple_reasonablyAligned => mkTuple ts (f := f) fl none init_off

private lemma tupleCursor_eq_zero_of_le {m n : Nat} (fsize falign : (i : Nat) → i < m → Nat)
    (h_sz : ∀ i (hi : i < m), i ≠ n → fsize i hi = 0) :
    ∀ k (hk : k ≤ m), k ≤ n → tupleCursor fsize falign 0 k hk = 0
  | 0, _, _ => rfl
  | k + 1, hk, hle => by
    have ih := tupleCursor_eq_zero_of_le fsize falign h_sz k (Nat.le_of_succ_le hk) (by omega)
    simp [tupleCursor, ih, h_sz k hk (by omega)]

private lemma tupleCursor_eq_of_gt {m n : Nat} (hn : n < m) (fsize falign : (i : Nat) → i < m → Nat)
    (h_sz : ∀ i (hi : i < m), i ≠ n → fsize i hi = 0)
    (h_al : ∀ i (hi : i < m), i ≠ n → falign i hi = 1) :
    ∀ k (hk : k ≤ m), n < k → tupleCursor fsize falign 0 k hk = fsize n hn
  | 0, _, hlt => nomatch hlt
  | k + 1, hk, hlt => by
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
    · have h0 := tupleCursor_eq_zero_of_le fsize falign h_sz n (Nat.le_of_succ_le hk) (Nat.le_refl n)
      simp [tupleCursor, h0]
    · have ih := tupleCursor_eq_of_gt hn fsize falign h_sz h_al k (Nat.le_of_succ_le hk) hlt'
      simp [tupleCursor, ih, h_al k hk (by omega), h_sz k hk (by omega)]

lemma mkTuple_transparent (ts : List MType) {f : TupleFlags}
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (n : Nat)
    (h_zst : ∀ i (hi : i < ts.length), i ≠ n →
      (fl i hi).size_and_align.size = 0 ∧ (fl i hi).size_and_align.align = 1) :
    (mkTuple ts (f := f) fl none 0).Transparent := by
  let fsize : (idx : Nat) → idx < ts.length → Nat := λ idx h ↦ (fl idx h).size
  let falign : (idx : Nat) → idx < ts.length → Nat := λ idx h ↦ effAlign none (fl idx h).size_and_align.align
  have h_sz : ∀ i (hi : i < ts.length), i ≠ n → fsize i hi = 0 := by
    intro i hi hne; have := (h_zst i hi hne).1; simp [fsize] at this ⊢; exact this
  have h_al : ∀ i (hi : i < ts.length), i ≠ n → falign i hi = 1 :=
    λ i hi hne ↦ (h_zst i hi hne).2
  have h_sa_zst : ∀ i (hi : i < ts.length), i ≠ n → (fl i hi).size_and_align = .zero_sized_minimally_aligned :=
    λ i hi hne ↦ SizeAndAlign.ext (h_zst i hi hne).1 (h_zst i hi hne).2
  by_cases hn : n < ts.length
  · have h_sa : tupleSizeAndAlign fsize falign 0 (by grind) = (fl n hn).size_and_align := by
      have h_max : natMax ts.length falign 1 = (fl n hn).size_and_align.align := by
        apply Nat.le_antisymm
        · apply lub_natMax
          · exact isPowerOfTwo_ge_one _ (fl n hn).size_and_align.wf_align
          · intro i hi
            by_cases hne : i = n
            · subst hne; exact Nat.le_refl _
            · rw [h_al i hi hne]
              exact isPowerOfTwo_ge_one _ (fl n hn).size_and_align.wf_align
        · exact le_natMax ts.length falign 1 n hn
      have h_cur := tupleCursor_eq_of_gt hn fsize falign h_sz h_al ts.length (Nat.le_refl _) hn
      ext
      · simp only [tupleSizeAndAlign, h_cur, h_max]
        simp only [fsize, ← size_known]
        exact alignUp_of_dvd (fl n hn).size_and_align.wf_size
      · simp [tupleSizeAndAlign, h_max]
    have h_off : tupleFieldOffset fsize falign 0 n hn = 0 := by
      simp [tupleFieldOffset, tupleCursor_eq_zero_of_le fsize falign h_sz n (by omega) (Nat.le_refl n)]
    dsimp only [mkTuple]
    rw [h_sa]
    exact .tuple_one_elem ts f _ fl n hn h_off h_sa_zst
  · have h_sa : tupleSizeAndAlign fsize falign 0 (by grind) = .zero_sized_minimally_aligned := by
      have h_max : natMax ts.length falign 1 = 1 := by
        apply Nat.le_antisymm
        · apply lub_natMax ts.length falign 1 1 (Nat.le_refl 1)
          intro i hi
          rw [h_al i hi (by omega)]
        · exact init_le_natMax ts.length falign 1
      have h_cur := tupleCursor_eq_zero_of_le fsize falign h_sz ts.length (Nat.le_refl _) (by omega)
      ext <;> simp [tupleSizeAndAlign, h_cur, h_max]
    dsimp only [mkTuple]
    rw [h_sa]
    exact .tuple_zero_sized ts f _ fl (λ i hi ↦ h_sa_zst i hi (by omega))

@[grind ←]
lemma mkTuple_packed (ts : List MType) {f : TupleFlags}
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (a : { a : Nat // a.isPowerOfTwo }) :
    (mkTuple ts (f := f) fl (.some a) 0).Packed a.val := by
  refine .tuple ts f _ fl id _ a.property (mkTuple_packed_bounds_align ts (f := f) fl a 0) Function.bijective_id ?_ ?_
    (tupleSizeAndAlign_size_eq_natMax _ _ _) ?_
  · intro i hle
    simp [tupleFieldOffset, tupleCursor, effAlign]
    grind
  · intro hl
    simp [tupleFieldOffset, tupleCursor]
  · grind

grind_pattern mkTuple_packed => mkTuple ts (f := f) fl (.some a) 0

@[grind ←]
lemma padVariantLayout_reasonablyAligned {t : MType} (cl : Layout t)
    (hcl : cl.ReasonablyAligned) (payload_off : Nat) (sa : SizeAndAlign)
    (h_align : cl.size_and_align.align ≤ sa.align) (h_dvd : sa.align ∣ payload_off) :
    (padVariantLayout cl payload_off sa).ReasonablyAligned :=
  match t, cl, hcl with
  | .int _, _, hcl | .enum _ _, _, hcl => hcl
  | .tuple ts f, .tuple _ vfl _, .tuple _ _ _ _ _ h_vtuple_aligned =>
    .tuple ts f _ vfl sa
      ⟨by grind,
       λ j hj ↦ by
         have : (vfl j hj).size_and_align.align ∣ sa.align := by grind
         grind [Nat.dvd_trans, Nat.dvd_add]⟩

@[grind ←]
lemma mkEnumCore_reasonablyAligned (tagTy : IUScalarTy) (shift_payload : Bool)
    (vs : List MType) {f : EnumFlags}
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).ReasonablyAligned) :
    (mkEnumCore tagTy shift_payload vs (f := f) cl).ReasonablyAligned :=
  .enum vs f _ _ _ _ (by grind [Nat.dvd_zero])

@[grind ←]
lemma mkEnum_reasonablyAligned (tagTy : IUScalarTy := .unsigned .Usize)
    (vs : List MType) {f : EnumFlags}
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).ReasonablyAligned) :
    (mkEnum tagTy vs (f := f) cl).ReasonablyAligned :=
  mkEnumCore_reasonablyAligned tagTy true vs cl h_cl

@[grind ←]
lemma mkEnumPrimitive_reasonablyAligned (tagTy : IUScalarTy)
    (vs : List MType) {f : EnumFlags}
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).ReasonablyAligned) :
    (mkEnumPrimitive tagTy vs (f := f) cl).ReasonablyAligned :=
  mkEnumCore_reasonablyAligned tagTy false vs cl h_cl

end ReprC

/-! ## `IsReprC` and Flag Satisfaction -/

@[grind]
inductive IsReprCTuple (init_off : Nat) :
    TupleAlignmentModifier → {t : MType} → Layout t → Prop where
  | reasonablyAligned (ts : List MType) (f : TupleFlags)
      (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) :
      IsReprCTuple init_off .reasonablyAligned (ReprC.mkTuple ts (f := f) fl none init_off)
  | packed (ts : List MType) (f : TupleFlags)
      (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
      (n : Nat) (hn : n.isPowerOfTwo) :
      IsReprCTuple init_off (.packed n hn) (ReprC.mkTuple ts (f := f) fl (.some ⟨n, hn⟩) init_off)
  | aligned (ts : List MType) (f : TupleFlags)
      (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
      (n : Nat) (hn : n.isPowerOfTwo) :
      IsReprCTuple init_off (.aligned n hn) ((ReprC.mkTuple ts (f := f) fl none init_off).alignTupleUp n hn)

grind_pattern IsReprCTuple.reasonablyAligned => ReprC.mkTuple ts (f := f) fl none init_off
grind_pattern IsReprCTuple.packed => ReprC.mkTuple ts (f := f) fl (.some ⟨n, hn⟩) init_off
grind_pattern IsReprCTuple.aligned => (ReprC.mkTuple ts (f := f) fl none init_off).alignTupleUp n hn

@[grind]
inductive IsReprCEnum (tagTy : IUScalarTy) :
    EnumAlignmentModifier → {t : MType} → Layout t → Prop where
  | reasonablyAligned (vs : List MType) (f : EnumFlags)
      (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (hcl : ∀ idx (h : idx < vs.length), IsReprCTuple 0 .reasonablyAligned (cl idx h)) :
      IsReprCEnum tagTy .reasonablyAligned (ReprC.mkEnum tagTy vs (f := f) cl)
  | aligned (vs : List MType) (f : EnumFlags)
      (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (hcl : ∀ idx (h : idx < vs.length), IsReprCTuple 0 .reasonablyAligned (cl idx h))
      (n : Nat) (hn : n.isPowerOfTwo) :
      IsReprCEnum tagTy (.aligned n hn) ((ReprC.mkEnum tagTy vs (f := f) cl).alignEnumUp n hn)

grind_pattern IsReprCEnum.reasonablyAligned => ReprC.mkEnum tagTy vs (f := f) cl
grind_pattern IsReprCEnum.reasonablyAligned => ReprC.mkEnumCore tagTy true vs (f := f) cl
grind_pattern IsReprCEnum.aligned => (ReprC.mkEnum tagTy vs (f := f) cl).alignEnumUp n hn
grind_pattern IsReprCEnum.aligned => (ReprC.mkEnumCore tagTy true vs (f := f) cl).alignEnumUp n hn

@[grind]
inductive IsReprPrimEnum (tagTy : IUScalarTy) :
    EnumAlignmentModifier → {t : MType} → Layout t → Prop where
  | reasonablyAligned (vs : List MType) (f : EnumFlags)
      (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (hcl : ∀ idx (h : idx < vs.length), IsReprCTuple tagTy.size .reasonablyAligned (cl idx h)) :
      IsReprPrimEnum tagTy .reasonablyAligned (ReprC.mkEnumPrimitive tagTy vs (f := f) cl)
  | aligned (vs : List MType) (f : EnumFlags)
      (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (hcl : ∀ idx (h : idx < vs.length), IsReprCTuple tagTy.size .reasonablyAligned (cl idx h))
      (n : Nat) (hn : n.isPowerOfTwo) :
      IsReprPrimEnum tagTy (.aligned n hn) ((ReprC.mkEnumPrimitive tagTy vs (f := f) cl).alignEnumUp n hn)

grind_pattern IsReprPrimEnum.reasonablyAligned => ReprC.mkEnumPrimitive tagTy vs (f := f) cl
grind_pattern IsReprPrimEnum.reasonablyAligned => ReprC.mkEnumCore tagTy false vs (f := f) cl
grind_pattern IsReprPrimEnum.aligned => (ReprC.mkEnumPrimitive tagTy vs (f := f) cl).alignEnumUp n hn
grind_pattern IsReprPrimEnum.aligned => (ReprC.mkEnumCore tagTy false vs (f := f) cl).alignEnumUp n hn

@[simp, grind =]
def satisfies : {ty : MType} → (l : Layout ty) → Prop
| .int _, _ => True
| .tuple _ ⟨.reprRust, .reasonablyAligned⟩, l => l.ReasonablyAligned
| .tuple _ ⟨.reprRust, .packed n _⟩, l => Packed n l
| .tuple _ ⟨.reprRust, .aligned n _⟩, l => l.ReasonablyAligned ∧ l.Aligned n
| .tuple _ ⟨.reprTransparent, .reasonablyAligned⟩, l => l.Transparent
| .tuple _ ⟨.reprTransparent, .packed _ _⟩, _ => False
| .tuple _ ⟨.reprTransparent, .aligned _ _⟩, _ => False
| .tuple _ ⟨.reprC, m⟩, l => l.IsReprCTuple 0 m
| .enum _ ⟨.reprRust, .reasonablyAligned⟩, l => l.ReasonablyAligned
| .enum _ ⟨.reprRust, .aligned n _⟩, l => l.ReasonablyAligned ∧ l.Aligned n
| .enum _ ⟨.reprC, m⟩, l => l.IsReprCEnum (.unsigned .Usize) m
| .enum _ ⟨.reprC_prim prim, m⟩, l => l.IsReprCEnum prim m
| .enum _ ⟨.reprPrim prim, m⟩, l => l.IsReprPrimEnum prim m

@[grind →]
lemma IsReprCTuple.reasonablyAligned_of {init_off : Nat} {t : MType} {l : Layout t}
    (h : l.IsReprCTuple init_off .reasonablyAligned) :
    l.ReasonablyAligned := by
  cases h with
  | reasonablyAligned ts f fl =>
    exact ReprC.mkTuple_reasonablyAligned ts fl init_off

@[grind →]
lemma IsReprCTuple.minOffset {init_off : Nat} {t : MType} {l : Layout t}
    (h : l.IsReprCTuple init_off .reasonablyAligned) :
    ReprC.TupleMinOffset init_off l := by
  cases h with
  | reasonablyAligned ts f fl =>
    exact ReprC.mkTuple_minOffset ts fl none init_off

lemma satisfies_isTuple_reasonablyAligned {t : MType} (ht : t.isTuple) (l : Layout t)
    (h : l.satisfies) : l.ReasonablyAligned := by
  cases ht; exact h

grind_pattern satisfies_isTuple_reasonablyAligned => t.isTuple, l.satisfies

@[grind →]
lemma satisfies_tuple_spec {ts f} (l : Layout (.tuple ts f)) :
  l.satisfies → match f.align with
  | .packed n _ => Packed n l
  | .aligned n _ => l.ReasonablyAligned ∧ l.Aligned n
  | .reasonablyAligned => l.ReasonablyAligned
:= by
  rcases f with ⟨repr, align⟩
  intro h
  cases repr <;> cases align <;> simp [satisfies] at h ⊢
  all_goals try exact h
  · cases h; grind
  · cases h; grind
  · cases h; grind
  · exact Transparent_ReasonablyAligned _ l h

@[grind →]
lemma satisfies_enum_spec {vs f} (l : Layout (.enum vs f)) :
  l.satisfies → match f.align with
  | .aligned n _ => l.ReasonablyAligned ∧ l.Aligned n
  | .reasonablyAligned => l.ReasonablyAligned
:= by
  rcases f with ⟨repr, align⟩
  intro h
  cases repr <;> cases align <;> simp [satisfies] at h ⊢
  all_goals try exact h
  all_goals (cases h; grind)

end Layout
end Aeneas
