module
public import Aeneas.Data.Layout.Reasonable
public section

namespace Aeneas

/-! ## Definitions (`LayoutInput` and `RichMType`) -/

inductive LayoutInput : MType → Type 0 where
| tuple
    (field_layouts : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) :
    LayoutInput (.tuple ts f)
| enum
    (variant_layout_inputs : (idx : Nat) → (h : idx < vs.length) → LayoutInput vs[idx]) :
    LayoutInput (.enum vs f)
| int :
    LayoutInput (.int i)

namespace LayoutInput

inductive Satisfies : (m : MType) → Layout m → LayoutInput m → Prop where
| tuple ts f fo fr fl sa :
  (∀ n (h : n < ts.length), fr n h = fl n h) →
  Satisfies (.tuple ts f) (.tuple fo fl sa) (.tuple fr)
| enum vs f vt vli vl d sa :
  (∀ n (h : n < vs.length), Satisfies vs[n] (vl n h) (vli n h)) →
  Satisfies (.enum vs f) (.enum vt vl d sa) (.enum vli)
| int i sa h : Satisfies (.int i) (.int sa h) .int

inductive TransparentValid : (m : MType) → LayoutInput m → Prop where
| tuple ts f fr :
  f.repr ≠ .reprTransparent →
  TransparentValid (.tuple ts f) (.tuple fr)
| tupleTransparent ts f fr n :
  f.repr = .reprTransparent →
  (∀ i hi, i ≠ n → let l := fr i hi; l.size_and_align.size = 0 ∧ l.size_and_align.align = 1) →
  TransparentValid (.tuple ts f) (.tuple fr)
| enum vs f vli :
  TransparentValid (.enum vs f) (.enum vli)
| int i : TransparentValid (.int i) .int

inductive Valid : (m : MType) → LayoutInput m → Prop where
| tuple ts f fl :
  (∀ i (hi : i < ts.length), (fl i hi).Valid) →
  Valid (.tuple ts f) (.tuple fl)
| enum vs f vli :
  (∀ i (hi : i < vs.length), Valid vs[i] (vli i hi)) →
  Valid (.enum vs f) (.enum vli)
| int i : Valid (.int i) .int

end LayoutInput

@[expose, reducible]
def RichMType := (m : MType) × LayoutInput m

namespace RichMType

  @[expose, simp, grind =, reducible] def mkTuple (ts : List ((m : MType) × Layout m)) (f : TupleFlags) : RichMType :=
    ⟨ .tuple (ts.map (·.1)) f, .tuple (λ i hi ↦ ((@List.getElem_map ((m : MType) × _) _ (·.1) ts i hi) ▸ (ts[i]'(by grind)).2)) ⟩

  @[expose, simp, grind =, reducible] def mkEnum (ts : List (List ((m : MType) × (Layout m)))) (f : EnumFlags) : RichMType :=
    let tuples := ts.map (mkTuple · {repr := .reprRust, align := .reasonablyAligned}) ;
    ⟨ .enum (tuples.map (·.1)) f, .enum (λ i hi ↦ ((@List.getElem_map ((m : MType) × _) _ (·.1) tuples i hi) ▸ (tuples[i]'(by grind)).2)) ⟩

  @[expose, simp, grind =, reducible]
  def IsValidLayoutForRichMType {ty : RichMType} (l : Layout ty.1) : Prop := l.Valid ∧ LayoutInput.Satisfies _ l ty.2

end RichMType

/-! ## Helper Definitions for Proving Inhabitance -/

namespace RichMType

  def example_layoutAux : {m : MType} → (li : LayoutInput m) → (init_off : Nat := 0) → Layout m
    | .int ty, .int, _ => .int ty.reasonablyAligned ty.reasonablyAligned_isReasonable
    | .tuple ts f, .tuple fl, init_off =>
      match f.align with
      | .reasonablyAligned => Layout.ReprC.mkTuple ts fl none init_off
      | .packed n hn => Layout.ReprC.mkTuple ts fl (.some ⟨n, hn⟩) init_off
      | .aligned n hn => (Layout.ReprC.mkTuple ts fl none init_off).alignTupleUp n hn
    | .enum vs f, .enum v_inh, _ =>
      let base : Layout (.enum vs f) :=
        match f.repr with
        | .reprRust | .reprC =>
          Layout.ReprC.mkEnum (.unsigned .Usize) vs (λ idx h ↦ example_layoutAux (v_inh idx h) 0)
        | .reprC_prim prim =>
          Layout.ReprC.mkEnum prim vs (λ idx h ↦ example_layoutAux (v_inh idx h) 0)
        | .reprPrim prim =>
          Layout.ReprC.mkEnumPrimitive prim vs (λ idx h ↦ example_layoutAux (v_inh idx h) prim.size)
      match f.align with
      | .reasonablyAligned => base
      | .aligned n hn => base.alignEnumUp n hn

  @[expose, simp, grind =, reducible]
  def example_layout (ty : RichMType) : Layout ty.1 :=
    example_layoutAux ty.2 0

end RichMType

/-! ## Typeclass Instances and Lemmas -/

namespace LayoutInput

attribute [class] Layout.Valid
attribute [instance] Layout.Valid.int

attribute [class] TransparentValid
attribute [instance] TransparentValid.enum
attribute [instance] TransparentValid.int

attribute [class] Valid
attribute [instance] Valid.int

lemma Valid.cast {m m' : MType} (h : m' = m) {li : LayoutInput m} (hli : li.Valid) :
    (h ▸ li).Valid := by
  subst h; exact hli

class AllValid {α : Type} (l : List α) (f : α → (m : MType) × LayoutInput m) : Prop where
  out : ∀ idx (h : idx < l.length), (f l[idx]).2.Valid

instance {α : Type} {f : α → (m : MType) × LayoutInput m} : AllValid [] f := ⟨λ _ h ↦ nomatch h⟩
instance {α : Type} {x : α} {xs : List α} {f : α → (m : MType) × LayoutInput m}
    [hx : (f x).2.Valid] [hxs : AllValid xs f] :
    AllValid (x :: xs) f :=
  ⟨λ | 0, _ => hx | n + 1, h => hxs.out n (Nat.lt_of_succ_lt_succ h)⟩

end LayoutInput

namespace Layout

lemma Valid.cast {m m' : MType} (h : m' = m) {l : Layout m} (hl : l.Valid) :
    (h ▸ l).Valid := by
  subst h; exact hl

class AllValid (l : List ((m : MType) × Layout m)) : Prop where
  out : ∀ idx (h : idx < l.length), l[idx].2.Valid

instance : AllValid [] := ⟨λ _ h ↦ nomatch h⟩
instance {x : (m : MType) × Layout m} {xs : List ((m : MType) × Layout m)}
    [hx : x.2.Valid] [hxs : AllValid xs] :
    AllValid (x :: xs) :=
  ⟨λ | 0, _ => hx | n + 1, h => hxs.out n (Nat.lt_of_succ_lt_succ h)⟩

end Layout

namespace RichMType

  instance {ts : List ((m : MType) × (Layout m))} {f} [h : MType.AllReasonable ts (·.1)] [hf : MType.TupleFlagsReasonable f] : (mkTuple ts f).1.Reasonable :=
    .tuple _ _ (by simp; apply h.out) hf

  instance {ts : List ((m : MType) × (Layout m))} {f} [h : Layout.AllValid ts] : (mkTuple ts f).2.Valid :=
    .tuple _ _ _ (λ i hi ↦ Layout.Valid.cast (@List.getElem_map ((m : MType) × _) _ (·.1) ts i hi) (h.out i (by grind)))

  instance {ts : List ((m : MType) × (Layout m))} {a} : (mkTuple ts {repr := .reprRust, align := a}).2.TransparentValid := by constructor; simp
  instance {ts : List ((m : MType) × (Layout m))} {a} : (mkTuple ts {repr := .reprC, align := a}).2.TransparentValid := by constructor; simp

  instance {ts : List (List ((m : MType) × (Layout m)))} {f}
    [hl : MType.ListLengthLe ts f.minMaxVariants]
    [h : MType.AllReasonable ts (λ x ↦ (mkTuple x {repr := .reprRust, align := .reasonablyAligned}).1)] : (mkEnum ts f).1.Reasonable := by
    constructor
    · simp only [List.length_map]
      exact Nat.le_trans hl.sound f.minMaxVariants_le_maxVariants
    · intros _ _; simp; constructor
    · simp; apply h.out

  instance {ts : List (List ((m : MType) × (Layout m)))} {f}
    [h : LayoutInput.AllValid ts (mkTuple · {repr := .reprRust, align := .reasonablyAligned})] :
    (mkEnum ts f).2.Valid :=
    .enum _ _ _ (λ i hi ↦ by
      apply LayoutInput.Valid.cast (@List.getElem_map ((m : MType) × _) _ (·.1) _ i hi)
      change ((ts.map (mkTuple · { repr := .reprRust, align := .reasonablyAligned }))[i]'(by grind)).2.Valid
      rw [List.getElem_map]
      exact h.out i (by grind))

  instance {ts f} : (mkEnum ts f).2.TransparentValid := by constructor

  private lemma example_layoutAux_isTuple_valid {t : MType} {li : LayoutInput t}
      (ht : t.isTuple) (h_valid : li.Valid) (init_off : Nat) :
      (example_layoutAux li init_off).Valid :=
    match t, ht, li, h_valid with
    | .tuple ts _, .tuple _, .tuple fl, .tuple _ _ _ h_fl =>
      Layout.ReprC.mkTuple_rust_valid ts fl init_off h_fl

  private lemma example_layoutAux_isTuple_isReprCTuple {t : MType} {li : LayoutInput t}
      (ht : t.isTuple) (init_off : Nat) :
      (example_layoutAux li init_off).IsReprCTuple init_off .reasonablyAligned :=
    match t, ht, li with
    | .tuple ts _, .tuple _, .tuple fl =>
      .reasonablyAligned ts ⟨.reprRust, .reasonablyAligned⟩ fl

  private lemma example_layoutAux_isTuple_padVariantLayout_satisfies {t : MType} {li : LayoutInput t}
      (ht : t.isTuple) (init_off payload_off : Nat) (sa : SizeAndAlign) :
      LayoutInput.Satisfies t (Layout.ReprC.padVariantLayout (example_layoutAux li init_off) payload_off sa) li :=
    match t, ht, li with
    | .tuple ts _, .tuple _, .tuple fl =>
      .tuple ts ⟨.reprRust, .reasonablyAligned⟩ _ fl fl sa (λ _ _ ↦ rfl)

  private lemma alignTupleUp_satisfies_aux {t : MType} (l : Layout t) (n : Nat) (hn : n.isPowerOfTwo) :
      let l' : Layout t := match t, l with
        | .tuple _ _, x => x.alignTupleUp n hn
        | _, x => x
      ∀ {li : LayoutInput t}, LayoutInput.Satisfies t l li → LayoutInput.Satisfies t l' li := by
    intro l' li h
    cases h with
    | tuple ts tf fo fr fl _ h_fr => exact .tuple ts tf fo fr fl _ h_fr
    | enum vs ef vt vli vl d sa h_vl => exact .enum vs ef vt vli vl d sa h_vl
    | int ti sa h => exact .int ti sa h

  private lemma alignEnumUp_satisfies {vs : List MType} {f : EnumFlags}
      {l : Layout (.enum vs f)} {li : LayoutInput (.enum vs f)}
      (n : Nat) (hn : n.isPowerOfTwo)
      (h : LayoutInput.Satisfies (.enum vs f) l li) :
      LayoutInput.Satisfies (.enum vs f) (l.alignEnumUp n hn) li := by
    cases h with
    | enum _ _ vt vli vl d sa h_vl =>
      exact .enum vs f vt vli _ d _ (λ i hi ↦ alignTupleUp_satisfies_aux (vl i hi) n hn (h_vl i hi))

  private lemma mkEnumCore_satisfies (tagTy : IUScalarTy) (shift_payload : Bool)
      (vs : List MType) {f : EnumFlags}
      (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
      (vli : (idx : Nat) → (h : idx < vs.length) → LayoutInput vs[idx])
      (init_off : Nat) :
      LayoutInput.Satisfies (.enum vs f)
        (Layout.ReprC.mkEnumCore tagTy shift_payload vs (λ idx h ↦ example_layoutAux (vli idx h) init_off))
        (.enum vli) :=
    .enum vs f _ vli _ _ _ (λ idx h ↦
      example_layoutAux_isTuple_padVariantLayout_satisfies (ht idx h) init_off _ _)

  lemma example_layout_IsValidLayoutForRichMType {ty : RichMType}
      [hr : ty.1.Reasonable] [hv : ty.2.Valid] [htr : ty.2.TransparentValid] :
      IsValidLayoutForRichMType (example_layout ty) := by
    rcases ty with ⟨m, li⟩
    cases hr with
    | int i =>
      cases li
      exact ⟨.int i _ _, .int i _ _⟩
    | tuple ts f _ flagsr =>
      cases li with
      | tuple fl =>
        cases hv with
        | tuple _ _ _ h_valid =>
          rcases f with ⟨repr, align⟩
          cases repr with
          | reprTransparent =>
              have h_align := flagsr.out rfl
              simp at h_align; subst align
              cases htr with
              | tuple _ _ _ h_ne => nomatch h_ne rfl
              | tupleTransparent _ _ _ n _ h_zst =>
                exact ⟨Layout.ReprC.mkTuple_transparent_valid ts fl n h_valid h_zst,
                       .tuple ts _ _ fl fl _ (λ _ _ ↦ rfl)⟩
          | reprC =>
            cases align with
            | reasonablyAligned =>
              exact ⟨Layout.ReprC.mkTuple_valid ts fl h_valid, .tuple ts _ _ fl fl _ (λ _ _ ↦ rfl)⟩
            | packed n hn =>
              exact ⟨Layout.ReprC.mkTuple_packed_valid ts fl n hn h_valid, .tuple ts _ _ fl fl _ (λ _ _ ↦ rfl)⟩
            | aligned n hn =>
              exact ⟨Layout.ReprC.mkTuple_aligned_valid ts fl n hn h_valid, .tuple ts _ _ fl fl _ (λ _ _ ↦ rfl)⟩
          | reprRust =>
            cases align with
            | reasonablyAligned =>
              exact ⟨Layout.ReprC.mkTuple_rust_valid ts fl 0 h_valid, .tuple ts _ _ fl fl _ (λ _ _ ↦ rfl)⟩
            | packed n hn =>
              exact ⟨Layout.ReprC.mkTuple_rust_packed_valid ts fl n hn h_valid, .tuple ts _ _ fl fl _ (λ _ _ ↦ rfl)⟩
            | aligned n hn =>
              exact ⟨Layout.ReprC.mkTuple_rust_aligned_valid ts fl n hn 0 h_valid, .tuple ts _ _ fl fl _ (λ _ _ ↦ rfl)⟩
    | enum vs f h_max ht _ =>
      cases li with
      | enum vli =>
        cases hv with
        | enum _ _ _ h_vli_valid =>
          have h_cl_valid (init_off : Nat) : ∀ idx (h : idx < vs.length), (example_layoutAux (vli idx h) init_off).Valid :=
            λ idx h ↦ example_layoutAux_isTuple_valid (ht idx h) (h_vli_valid idx h) init_off
          have h_cl_reprC (init_off : Nat) : ∀ idx (h : idx < vs.length), (example_layoutAux (vli idx h) init_off).IsReprCTuple init_off .reasonablyAligned :=
            λ idx h ↦ example_layoutAux_isTuple_isReprCTuple (ht idx h) init_off
          rcases f with ⟨repr, align⟩
          cases repr with
          | reprRust =>
            have h_max' : vs.length ≤ 2 ^ (IUScalarTy.unsigned .Usize).numBits := by grind
            cases align with
            | reasonablyAligned =>
              exact ⟨Layout.ReprC.mkEnum_rust_valid (.unsigned .Usize) vs h_max' ht _ (h_cl_valid 0),
                     mkEnumCore_satisfies (.unsigned .Usize) true vs ht vli 0⟩
            | aligned n hn =>
              exact ⟨Layout.ReprC.mkEnum_rust_aligned_valid (.unsigned .Usize) vs h_max' ht _ n hn (h_cl_valid 0),
                     alignEnumUp_satisfies n hn (mkEnumCore_satisfies (.unsigned .Usize) true vs ht vli 0)⟩
          | reprC =>
            have h_max' : vs.length ≤ 2 ^ (IUScalarTy.unsigned .Usize).numBits := by grind
            cases align with
            | reasonablyAligned =>
              exact ⟨Layout.ReprC.mkEnum_valid vs h_max' ht _ (h_cl_valid 0) (h_cl_reprC 0),
                     mkEnumCore_satisfies (.unsigned .Usize) true vs ht vli 0⟩
            | aligned n hn =>
              exact ⟨Layout.ReprC.mkEnum_aligned_valid vs h_max' ht _ n hn (h_cl_valid 0) (h_cl_reprC 0),
                     alignEnumUp_satisfies n hn (mkEnumCore_satisfies (.unsigned .Usize) true vs ht vli 0)⟩
          | reprC_prim prim =>
            cases align with
            | reasonablyAligned =>
              exact ⟨Layout.ReprC.mkEnum_prim_valid prim vs h_max ht _ (h_cl_valid 0) (h_cl_reprC 0),
                     mkEnumCore_satisfies prim true vs ht vli 0⟩
            | aligned n hn =>
              exact ⟨Layout.ReprC.mkEnum_prim_aligned_valid prim vs h_max ht _ n hn (h_cl_valid 0) (h_cl_reprC 0),
                     alignEnumUp_satisfies n hn (mkEnumCore_satisfies prim true vs ht vli 0)⟩
          | reprPrim prim =>
            cases align with
            | reasonablyAligned =>
              exact ⟨Layout.ReprC.mkEnumPrimitive_valid prim vs h_max ht _ (h_cl_valid prim.size) (h_cl_reprC prim.size),
                     mkEnumCore_satisfies prim false vs ht vli prim.size⟩
            | aligned n hn =>
              exact ⟨Layout.ReprC.mkEnumPrimitive_aligned_valid prim vs h_max ht _ n hn (h_cl_valid prim.size) (h_cl_reprC prim.size),
                     alignEnumUp_satisfies n hn (mkEnumCore_satisfies prim false vs ht vli prim.size)⟩

end RichMType

end Aeneas
