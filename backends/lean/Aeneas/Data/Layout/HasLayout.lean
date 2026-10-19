module
public import Aeneas.Data.Layout.Prelims
public import Aeneas.Data.Layout.Bytes
public import Aeneas.Data.Layout.MTypes
public import Aeneas.Data.Layout.Defs
public import Aeneas.Data.Layout.GaloisConnection
public import Aeneas.Data.Layout.ReprC
public section

namespace Aeneas

inductive LayoutKind where
| reprRust
| reprC
| reprC_prim (prim : IUScalarTy)
| reprPrim (prim : IUScalarTy)
| reprTransparent

inductive LayoutModifier where
| packed (n : Nat) (hn : n.isPowerOfTwo)
| aligned (n : Nat) (hn : n.isPowerOfTwo)
| reasonablyAligned -- in the absence of repr(packed) and repr(aligned) we just get a "reasonably aligned" layout.

namespace Layout

inductive IsReprCTuple (init_off : Nat) :
    LayoutModifier → {t : MType} → Layout t → Prop where
  | reasonablyAligned (ts : List MType) (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) :
      IsReprCTuple init_off .reasonablyAligned (ReprC.mkTuple ts fl none init_off)
  | packed (ts : List MType) (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
      (n : Nat) (hn : n.isPowerOfTwo) :
      IsReprCTuple init_off (.packed n hn) (ReprC.mkTuple ts fl (.some ⟨n, hn⟩) init_off)
  | aligned (ts : List MType) (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
      (n : Nat) (hn : n.isPowerOfTwo) :
      IsReprCTuple init_off (.aligned n hn) ((ReprC.mkTuple ts fl none init_off).alignTupleUp n hn)

inductive IsReprCEnum (tagTy : IUScalarTy) :
    LayoutModifier → {t : MType} → Layout t → Prop where
  | reasonablyAligned (vs : List MType)
      (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (hcl : ∀ idx (h : idx < vs.length), IsReprCTuple 0 .reasonablyAligned (cl idx h)) :
      IsReprCEnum tagTy .reasonablyAligned (ReprC.mkEnum tagTy vs cl)
  | aligned (vs : List MType)
      (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (hcl : ∀ idx (h : idx < vs.length), IsReprCTuple 0 .reasonablyAligned (cl idx h))
      (n : Nat) (hn : n.isPowerOfTwo) (ht : vs.Forall MType.isTuple) :
      IsReprCEnum tagTy (.aligned n hn) ((ReprC.mkEnum tagTy vs cl).alignEnumUp n hn ht)

inductive IsReprPrimEnum (tagTy : IUScalarTy) :
    LayoutModifier → {t : MType} → Layout t → Prop where
  | reasonablyAligned (vs : List MType)
      (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (hcl : ∀ idx (h : idx < vs.length), IsReprCTuple tagTy.size .reasonablyAligned (cl idx h)) :
      IsReprPrimEnum tagTy .reasonablyAligned (ReprC.mkEnumPrimitive tagTy vs cl)
  | aligned (vs : List MType)
      (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (hcl : ∀ idx (h : idx < vs.length), IsReprCTuple tagTy.size .reasonablyAligned (cl idx h))
      (n : Nat) (hn : n.isPowerOfTwo) (ht : vs.Forall MType.isTuple) :
      IsReprPrimEnum tagTy (.aligned n hn) ((ReprC.mkEnumPrimitive tagTy vs cl).alignEnumUp n hn ht)

@[simp, grind =]
def satisfies : {ty : MType} → (l : Layout ty) → (k : LayoutKind) → (m : LayoutModifier) → Prop
| _, l, .reprRust, .packed n _ => Packed n l
| _, l, .reprRust, .aligned n _ => l.ReasonablyAligned ∧ l.Aligned n
| _, l, .reprRust, .reasonablyAligned => l.ReasonablyAligned
| _, l, .reprTransparent, .reasonablyAligned => l.Transparent
| _, _, .reprTransparent, _ => False
| .tuple _, l, .reprC, m => l.IsReprCTuple 0 m
| .tuple _, _, .reprC_prim _, _ => False
| .tuple _, _, .reprPrim _, _ => False
| .enum _, l, .reprC, m => l.IsReprCEnum (.unsigned .Usize) m
| .enum _, l, .reprC_prim prim, m => l.IsReprCEnum prim m
| .enum _, l, .reprPrim prim, m => l.IsReprPrimEnum prim m
| .int _, _, _, _ => False

@[expose, simp]
def satisfiable : (ty : MType) → (k : LayoutKind) → (m : LayoutModifier) → Prop
| _, .reprRust, .reasonablyAligned => True   -- you can always be the default
| .tuple _, .reprRust, .packed _ _ => True   -- tuples can be repr(Rust, packed)
| .tuple _, .reprRust, .aligned _ _ => True  -- tuples can be repr(Rust, aligned)
| .enum _, .reprRust, .aligned _ _ => True   -- enums can be repr(Rust, aligned)
| .int _, _, _ => False                      -- integers do not take alignment specifiers
| _, .reprTransparent, _ => False            -- repr(transparent) is special and not handled here
| .tuple _, .reprC, _ => True                -- tuples can be repr(C) with packed and aligned
| .tuple _, .reprC_prim _, _ => False        -- tuples can not be repr(C, i8)
| .tuple _, .reprPrim _, _ => False          -- tuples can not be repr(i8)
| .enum _, _, .packed _ _ => False           -- enums can never be repr(packed)
| .enum _, .reprC, _ => True                 -- enums can be repr(C) or repr(C, aligned)
| .enum _, .reprC_prim _, _ => True          -- enums can be repr(C, i8) or repr(C, i8, aligned)
| .enum _, .reprPrim _,  _ => True           -- enums can be repr(i8) or repr(i8, aligned)

@[grind →]
lemma IsReprCTuple.isTuple_and_reasonablyAligned {init_off : Nat} {t : MType} {l : Layout t}
    (h : l.IsReprCTuple init_off .reasonablyAligned) :
    t.isTuple ∧ l.ReasonablyAligned := by
  cases h with
  | reasonablyAligned ts fl =>
    exact ⟨.tuple ts, ReprC.mkTuple_reasonablyAligned ts fl init_off⟩

@[grind →]
lemma satisfies_spec ty (l : Layout ty) k m :
  satisfies l k m → match m with
  | .packed n _ => Packed n l
  | .aligned n _ => l.ReasonablyAligned ∧ l.Aligned n
  | .reasonablyAligned => l.ReasonablyAligned
:= by
  intro h
  cases k with
  | reprRust => cases m <;> exact h
  | reprTransparent => cases m <;> grind
  | reprC => cases ty <;> cases h <;> grind
  | reprC_prim prim => cases ty <;> cases h <;> grind
  | reprPrim prim => cases ty <;> cases h <;> grind

end Layout

inductive LayoutInput : MType → Type 0 where
| tuple
    (field_layouts : (idx : Nat) → (h : idx < ts.length) → (Layout ts[idx] → Prop)) :
    LayoutInput (.tuple ts)
| enum
    (variant_layout_inputs : (idx : Nat) → (h : idx < vs.length) → LayoutInput vs[idx]) :
    LayoutInput (.enum vs)
| int :
    LayoutInput (.int i)

namespace LayoutInput

inductive Satisfies : (m : MType) → Layout m → LayoutInput m → Prop where
| tuple ts fo fr fl sa :
  (∀ n (h : n < ts.length), fr n h (fl n h)) →
  Satisfies (.tuple ts) (.tuple fo fl sa) (.tuple fr)
| enum vs vt vli vl d sa :
  (∀ n (h : n < vs.length), Satisfies vs[n] (vl n h) (vli n h)) →
  Satisfies (.enum vs) (.enum vt vl d sa) (.enum vli)

end LayoutInput

@[expose]
def RichMType := (m : MType) × LayoutInput m

namespace RichMType

  @[expose, simp, grind =, reducible] def mkTuple (ts : List ((m : MType) × (Layout m → Prop))) : RichMType :=
    ⟨ .tuple (ts.map (·.1)), .tuple (λ i hi l ↦ ((@List.getElem_map ((m : MType) × _) _ (·.1) ts i hi) ▸ (ts[i]'(by grind)).2) l) ⟩

  instance {ts : List ((m : MType) × (Layout m → Prop))} [h : MType.AllReasonable ts (·.1)] : (mkTuple ts).1.Reasonable :=
    .tuple _ (by simp; apply h.out)

  @[expose, simp, grind =, reducible] def mkEnum (ts : List (List ((m : MType) × (Layout m → Prop)))) : RichMType :=
    let tuples := ts.map mkTuple;
    ⟨ .enum (tuples.map (·.1)), .enum (λ i hi ↦ ((@List.getElem_map ((m : MType) × _) _ (·.1) tuples i hi) ▸ (tuples[i]'(by grind)).2)) ⟩

  instance {ts : List (List ((m : MType) × (Layout m → Prop)))}
    [hl : MType.ListLengthLe ts 4294967295] -- this is an astronomical bound
    [h : MType.AllReasonable ts (λ x ↦ (mkTuple x).1)] : (mkEnum ts).1.Reasonable := by
    constructor
    · have := hl.sound
      rcases System.Platform.numBits_eq with hb | hb <;> simp [Std.Usize.max, Std.Usize.numBits, hb] <;> omega
    · intros _ _; simp; constructor
    · simp; apply h.out

end RichMType


/-! ## The `HasLayout` Type Class -/

macro "has_layout_retract_embed" : tactic => `(tactic| (
  intro x
  cases x
  repeat cases ‹_ × _›
  all_goals simp
))

macro "has_layout_embed_retract" : tactic => `(tactic| (
  intro ⟨v, h⟩
  have h' := h
  cases h'
  all_goals (
    simp [List.map] at *
    repeat' (
      first
      | exact False.elim (MVal.valid_for.empty_elim ‹_›)
      | (cases ‹Nat› <;> dsimp (config := { iota := false, beta := false, zeta := false, proj := false }) only [Nat.zero_eq, Nat.succ_eq_add_one, List.getElem_cons_succ, List.getElem_cons_zero] at *)
    )
    all_goals (
      try cases ‹MVal.valid_for _ (.tuple _)›
      repeat cases ‹List.Forall₂ _ _ _›
      simp
    )
  )
))

/-! Type class associating a Lean type `α` with its machine `MType`.
    Lowering must be bijective. -/
class HasLayout (α : Type u) where
  rty : RichMType
  embed : α → { v : MVal // v.valid_for rty.1 }
  retract : { v : MVal // v.valid_for rty.1 } → α
  layout_meta : LayoutKind × LayoutModifier
  reasonable : rty.1.Reasonable := by infer_instance
  retract_embed : ∀ x, retract (embed x) = x := by has_layout_retract_embed
  embed_retract : ∀ v, embed (retract v) = v := by has_layout_embed_retract
  layout_meta_reasonable : Layout.satisfiable rty.1 layout_meta.1 layout_meta.2 := by simp [Layout.satisfiable] <;> trivial
  -- ... constraints on allowed_layout

namespace HasLayout

instance {α : Type u} [h : HasLayout α] : ((HasLayout.rty α).1).Reasonable :=
  h.reasonable

@[expose, simp, grind =] def ty (α : Type u) [h : HasLayout α] : MType := h.rty.1


def valid_layouts (α : Type u) [h : HasLayout α] (l : Layout (ty α)) : Prop :=
  l.satisfies (layout_meta α).1 (layout_meta α).2 ∧ LayoutInput.Satisfies _ l (rty α).2

@[expose, reducible] def xty (α : Type u) [h : HasLayout α] : ((m : MType) × (Layout m → Prop)) := ⟨ty α, valid_layouts α⟩


instance {α : Type u} [h : HasLayout α] : ((xty α).1).Reasonable :=
  h.reasonable

attribute [simp] retract_embed embed_retract

@[simp] theorem embed_valid {α : Type u} [HasLayout α] (x : α) :
    (embed x).val.valid_for (ty α) :=
  (embed x).property

@[expose, inline, simp]
def mkTuple {ts : List MType} (vs : List MVal)
    (h : List.Forall₂ MVal.valid_for vs ts := by simp <;> grind) :
    { v : MVal // v.valid_for (.tuple ts) } :=
  ⟨.tuple vs, .tuple vs ts h⟩

@[expose, inline, simp]
def mkVariant {ts : List MType} (d : Nat) (v : MVal)
    (hb : d < ts.length := by simp <;> grind)
    (hv : v.valid_for (ts[d]'hb) := by constructor; simp <;> grind) :
    { v : MVal // v.valid_for (.enum ts) } :=
  ⟨.variant d v, .enum d v ts hb hv⟩

-- Instances for primitive scalars and standard types

instance {ty : Std.UScalarTy} : HasLayout (Std.UScalar ty) where
  rty := ⟨.int (.unsigned ty), .int⟩
  embed := λ x ↦ ⟨.int x.val, .int ⟨x, rfl⟩⟩
  retract := λ | ⟨.int n, _⟩ => ⟨.ofNat ty.numBits n.toNat⟩
  layout_meta := (.reprRust, .reasonablyAligned)
  retract_embed := λ x ↦ by cases x; simp
  embed_retract v := match v with
    | ⟨.int n, .int ⟨x, h_eq⟩⟩ => by simp only [←h_eq, IUScalar.val, Std.UScalar.val, BitVec.ofNat_toNat, Int.toNat_natCast, BitVec.setWidth_eq]

instance {ty : Std.IScalarTy} : HasLayout (Std.IScalar ty) where
  rty := ⟨.int (.signed ty), .int ⟩
  embed := λ x ↦ ⟨.int x.val, .int ⟨x, rfl⟩⟩
  retract := λ | ⟨.int n, _⟩ => ⟨.ofInt ty.numBits n⟩
  layout_meta := (.reprRust, .reasonablyAligned)
  retract_embed := λ x ↦ by cases x; simp
  embed_retract v := match v with
    | ⟨.int n, .int ⟨x, h_eq⟩⟩ => by simp only [←h_eq, IUScalar.val, Std.IScalar.val, BitVec.ofInt_toInt]

instance : HasLayout Unit where
  rty := RichMType.mkTuple []
  embed := λ _ ↦ mkTuple []
  retract := λ _ ↦ ()
  layout_meta := (.reprRust, .reasonablyAligned)


instance : HasLayout Bool where
  rty := RichMType.mkEnum [[], []]
  embed := λ | true => mkVariant 0 (.tuple [])
             | false => mkVariant 1 (.tuple [])
  retract := λ | ⟨.variant 0 _, _⟩ => true
               | ⟨.variant 1 _, _⟩ => false
  layout_meta := (.reprRust, .reasonablyAligned)

instance {T1 : Type u} {T2 : Type v} [HasLayout T1] [HasLayout T2] : HasLayout (T1 × T2) where
  rty := RichMType.mkTuple [xty T1, xty T2]
  embed := λ (x0, x1) => mkTuple [embed x0, embed x1]
  retract := λ | ⟨.tuple [x0, x1], h⟩ =>
                  (retract (h.field 0), retract (h.field 1))
  layout_meta := (.reprRust, .reasonablyAligned)

instance {T1 : Type u} [HasLayout T1] : HasLayout (Option T1) where
  rty := RichMType.mkEnum [[], [xty T1]]
  embed := λ | .none => mkVariant 0 (.tuple [])
             | .some x => mkVariant 1 (.tuple [embed x])
  retract := λ | ⟨.variant 0 (.tuple []), _⟩ => .none
               | ⟨.variant 1 (.tuple [v0]), h⟩ =>
                  .some (retract (h.vfield 0 rfl))
  layout_meta := (.reprRust, .reasonablyAligned)

end HasLayout

end Aeneas
