module
public import Aeneas.Data.Layout.Prelims
public import Aeneas.Data.Layout.Bytes
public import Aeneas.Data.Layout.MTypes
public import Aeneas.Data.Layout.Defs
public import Aeneas.Data.Layout.EncodeDecode
public import Aeneas.Data.Layout.ReprC
public import Aeneas.Data.Layout.Properties
public import Aeneas.Data.Layout.Valid
public import Aeneas.Data.Layout.GaloisConnection
public import Aeneas.Data.Layout.Reasonable
public import Aeneas.Data.Layout.RichMTypes
public section

namespace Aeneas

/-! ## The `HasLayout` Type Class -/

macro "has_layout_retract_embed" : tactic =>
  let rty := Lean.mkIdent `Aeneas.HasLayout.rty
  let embed := Lean.mkIdent `Aeneas.HasLayout.embed
  let retract := Lean.mkIdent `Aeneas.HasLayout.retract
  `(tactic| (
    intro x
    cases x
    repeat cases ‹_ × _›
    all_goals simp [-$rty:ident, -$embed:ident, -$retract:ident]
  ))

macro "has_layout_embed_retract" : tactic =>
  let rty := Lean.mkIdent `Aeneas.HasLayout.rty
  let embed := Lean.mkIdent `Aeneas.HasLayout.embed
  let retract := Lean.mkIdent `Aeneas.HasLayout.retract
  let retract_iff := Lean.mkIdent `Aeneas.HasLayout.retract_eq_some_iff
  `(tactic| (
    intro ⟨v, h⟩ x h_ret
    have h' := h
    dsimp only [RichMType.mkTuple, RichMType.mkEnum, List.map] at h'
    cases h'
    all_goals (
      repeat' (
        first
        | exact False.elim (MVal.valid_for.empty_elim ‹_›)
        | (cases ‹Nat› <;> dsimp (config := { iota := false, beta := false, zeta := false, proj := false }) only [Nat.zero_eq, Nat.succ_eq_add_one, List.getElem_cons_succ, List.getElem_cons_zero] at *)
      )
      all_goals (
        try cases ‹MVal.valid_for _ (.tuple _ _)›
        repeat cases ‹List.Forall₂ _ _ _›
        simp [-$rty:ident, -$embed:ident, -$retract:ident, Option.bind_eq_some_iff, $retract_iff:ident, Subtype.ext_iff] at h_ret
        repeat' (first | cases ‹∃ _, _› | cases ‹_ ∧ _› | cases ‹_ ∨ _›)
        all_goals (
          try subst x
          simp [-$rty:ident, -$embed:ident, -$retract:ident, *]
        )
      )
    )
  ))

@[grind =]
noncomputable def valid_layouts_inhabitant (x : RichMType) [x.1.Reasonable] [x.2.Valid] [x.2.TransparentValid]: { l : Layout x.1 // x.IsValidLayoutForRichMType l} :=
  ⟨
    x.example_layout,
    RichMType.example_layout_IsValidLayoutForRichMType
  ⟩

/-! Type class associating a Lean type `α` with its machine `MType`.
    Lowering must be a partial bijection (`retract ∘ embed = some`). -/
class HasLayout (α : Type u) where
  rty : RichMType
  embed : α → { v : MVal // v.valid_for rty.1 }
  retract : { v : MVal // v.valid_for rty.1 } → Option α
  reasonable : rty.1.Reasonable := by infer_instance
  valid : rty.2.Valid := by infer_instance
  retract_embed : ∀ x, retract (embed x) = some x := by has_layout_retract_embed
  embed_retract : ∀ v x, retract v = some x → embed x = v := by has_layout_embed_retract
  transparent_valid : rty.2.TransparentValid := by infer_instance
  valid_layout : Layout rty.1 → Prop := rty.IsValidLayoutForRichMType
  valid_layout_inhab : { l // valid_layout l} := by apply valid_layouts_inhabitant
  valid_layout_sound : ∀ l, valid_layout l → rty.IsValidLayoutForRichMType l := by exact λ _ ↦ id

namespace HasLayout

instance {α : Type u} [h : HasLayout α] : ((HasLayout.rty α).1).Reasonable :=
  h.reasonable

instance {α : Type u} [h : HasLayout α] : (HasLayout.rty α).2.Valid :=
  h.valid

instance {α : Type u} [h : HasLayout α] : (HasLayout.rty α).2.TransparentValid :=
  h.transparent_valid

@[expose, simp, grind =] def ty (α : Type u) [h : HasLayout α] : MType := h.rty.1

noncomputable def the_layout (α : Type u) [h : HasLayout α] : { l : Layout (ty α) // h.valid_layout l } := Classical.choice (Nonempty.intro h.valid_layout_inhab)

@[expose, reducible] noncomputable def xty (α : Type u) [h : HasLayout α] : ((m : MType) × Layout m) := ⟨ty α, the_layout α⟩

instance {α : Type u} [h : HasLayout α] : ((xty α).1).Reasonable :=
  h.reasonable

instance {α : Type u} [h : HasLayout α] : (xty α).2.Valid :=
  (h.valid_layout_sound _ (the_layout α).2).1

attribute [simp] retract_embed
attribute [simp low, grind =] rty embed retract valid_layout

theorem retract_eq_some_iff {α : Type u} [HasLayout α] (v : { v : MVal // v.valid_for (ty α) }) (x : α) :
    retract v = some x ↔ embed x = v :=
  ⟨embed_retract v x, λ h ↦ h ▸ retract_embed x⟩

@[simp] theorem embed_valid {α : Type u} [HasLayout α] (x : α) :
    (embed x).val.valid_for (ty α) :=
  (embed x).property

@[expose, inline, simp]
def mkTuple {ts : List MType} {f} (vs : List MVal)
    (h : List.Forall₂ MVal.valid_for vs ts := by simp [-HasLayout.rty, -HasLayout.embed, -HasLayout.retract] <;> grind) :
    { v : MVal // v.valid_for (.tuple ts f) } :=
  ⟨.tuple vs, .tuple vs ts h⟩

@[expose, inline, simp]
def mkVariant {ts : List MType} {f} (d : Nat) (v : MVal)
    (hb : d < ts.length := by simp [-HasLayout.rty, -HasLayout.embed, -HasLayout.retract] <;> grind)
    (hv : v.valid_for (ts[d]'hb) := by constructor; simp [-HasLayout.rty, -HasLayout.embed, -HasLayout.retract] <;> grind) :
    { v : MVal // v.valid_for (.enum ts f) } :=
  ⟨.variant d v, .enum d v ts hb hv⟩

-- Instances for primitive scalars and standard types

noncomputable instance {ty : Std.UScalarTy} : HasLayout (Std.UScalar ty) where
  rty := ⟨.int (.unsigned ty), .int⟩
  embed := λ x ↦ ⟨.int x.val, .int ⟨x, rfl⟩⟩
  retract := λ | ⟨.int n, _⟩ => some ⟨.ofNat ty.numBits n.toNat⟩
  retract_embed := λ x ↦ by cases x; simp
  embed_retract v _ h_ret := match v, h_ret with
    | ⟨.int n, .int ⟨x, h_eq⟩⟩, rfl => by
      simp only [←h_eq, IUScalar.val, Std.UScalar.val, BitVec.ofNat_toNat, Int.toNat_natCast, BitVec.setWidth_eq]

noncomputable instance {ty : Std.IScalarTy} : HasLayout (Std.IScalar ty) where
  rty := ⟨.int (.signed ty), .int ⟩
  embed := λ x ↦ ⟨.int x.val, .int ⟨x, rfl⟩⟩
  retract := λ | ⟨.int n, _⟩ => some ⟨.ofInt ty.numBits n⟩
  retract_embed := λ x ↦ by cases x; simp
  embed_retract v _ h_ret := match v, h_ret with
    | ⟨.int n, .int ⟨x, h_eq⟩⟩, rfl => by
      simp only [←h_eq, IUScalar.val, Std.IScalar.val, BitVec.ofInt_toInt]

noncomputable instance : HasLayout Unit where
  rty := RichMType.mkTuple [] { repr := .reprRust, align := .reasonablyAligned }
  embed := λ _ ↦ mkTuple []
  retract := λ _ ↦ do return ()


noncomputable instance : HasLayout Bool where
  rty := RichMType.mkEnum [[], []] { repr := .reprRust, align := .reasonablyAligned }
  embed := λ | true => mkVariant 0 (.tuple [])
             | false => mkVariant 1 (.tuple [])
  retract := λ | ⟨.variant 0 _, _⟩ => do return true
               | ⟨.variant 1 _, _⟩ => do return false

noncomputable instance {T1 : Type u} {T2 : Type v} [HasLayout T1] [HasLayout T2] : HasLayout (T1 × T2) where
  rty := RichMType.mkTuple [xty T1, xty T2] { repr := .reprRust, align := .reasonablyAligned }
  embed := λ (x0, x1) => mkTuple [embed x0, embed x1]
  retract := λ | ⟨.tuple [x0, x1], h⟩ =>
                  (retract (h.field 0)).bind λ x0 ↦
                  (retract (h.field 1)).bind λ x1 ↦
                  some (x0, x1)

noncomputable instance {T1 : Type u} [HasLayout T1] : HasLayout (Option T1) where
  rty := RichMType.mkEnum [[], [xty T1]] { repr := .reprRust, align := .reasonablyAligned }
  embed := λ | .none => mkVariant 0 (.tuple [])
             | .some x => mkVariant 1 (.tuple [embed x])
  retract := λ | ⟨.variant 0 (.tuple []), _⟩ => do return .none
               | ⟨.variant 1 (.tuple [v0]), h⟩ => do
                  return .some (← retract (h.vfield 0 rfl))

end HasLayout

end Aeneas
