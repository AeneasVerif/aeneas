module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Array.Array
public section

namespace Aeneas

inductive IUScalarTy where
  | signed (ty : Std.IScalarTy)
  | unsigned (ty : Std.UScalarTy)

@[expose, implicit_reducible]
def IUScalarTy.numBits (ty : IUScalarTy) : Nat :=
  match ty with
  | .signed ty => ty.numBits
  | .unsigned ty => ty.numBits

@[expose, implicit_reducible]
def IUScalar (ty : IUScalarTy) : Type :=
  match ty with
  | .signed ty => Std.IScalar ty
  | .unsigned ty => Std.UScalar ty

@[expose] def IUScalar.bv {ty} (x : IUScalar ty) : BitVec ty.numBits :=
  match ty with
  | .signed _ => Std.IScalar.bv x
  | .unsigned _ => Std.UScalar.bv x
@[expose] def IUScalar.val {ty} (x : IUScalar ty) : ℤ :=
  match ty with
  | .signed _ => Std.IScalar.val x
  | .unsigned _ => Std.UScalar.val x

inductive MVal where
  | int (i : ℤ)
  | tuple (vs : List MVal)
  | variant (d : Nat) (data : MVal)

inductive MType where
  | int (ty : IUScalarTy)
  | tuple (fields : List MType)
  | enum (variants : List MType)

def MType.inhabited : MType → Bool
  | .int _ => true
  | .tuple ts => ts.attach.all (λ ⟨t, _⟩ ↦ t.inhabited)
  | .enum vs => vs.attach.any (λ ⟨v, _⟩ ↦ v.inhabited)

inductive MVal.valid_for : (v : MVal) → (ty : MType) → Prop where
  | int (st : IUScalarTy) (vv : IUScalar st) : i = vv.val → MVal.valid_for (.int i) (.int st)
  | tuple vs ts : List.Forall₂ MVal.valid_for vs ts → MVal.valid_for (.tuple vs) (.tuple ts)
  | enum (dv : Nat) v ts (hb : dv < ts.length) :
      MVal.valid_for v ts[dv] →
      MVal.valid_for (.variant dv v) (.enum ts)

attribute [simp] MVal.valid_for.int MVal.valid_for.tuple MVal.valid_for.enum

theorem MVal.valid_for.tuple_len {vs ts} (h : MVal.valid_for (.tuple vs) (.tuple ts)) :
    vs.length = ts.length :=
  match h with | .tuple _ _ f => f.length_eq

theorem MVal.valid_for.tuple_proj {vs ts} (h : MVal.valid_for (.tuple vs) (.tuple ts)) (idx : Fin vs.length) :
    MVal.valid_for vs[idx] (ts[idx]'(by rw [←h.tuple_len]; exact idx.isLt)) :=
  match h with | .tuple _ _ f => f.get _ _

theorem MVal.valid_for.variant_bound {d v ts} (h : MVal.valid_for (.variant d v) (.enum ts)) :
    d < ts.length :=
  match h with | .enum _ _ _ hb _ => hb

theorem MVal.valid_for.variant_proj {d v ts} (h : MVal.valid_for (.variant d v) (.enum ts)) :
    v.valid_for (ts[d]'(h.variant_bound)) :=
  match h with | .enum _ _ _ _ hv => hv

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
    repeat' (
      first
      | (clear ‹MVal.valid_for _ _›; simp only [List.length_cons, List.length_nil] at *; omega)
      | (cases ‹Nat› <;> dsimp (config := { iota := false, beta := false, proj := false, zeta := false }) only [Nat.zero_eq, Nat.succ_eq_add_one, List.getElem_cons_succ, List.getElem_cons_zero] at *)
    )
    all_goals (
      try cases ‹MVal.valid_for _ (.tuple _)›
      repeat cases ‹List.Forall₂ _ _ _›
      simp
    )
  )
))

/-- Type class associating a Lean type `α` with its mid-level `MType`. -/
class HasLayout (α : Type u) where
  ty : MType
  embed : α → { v : MVal // v.valid_for ty }
  retract : { v : MVal // v.valid_for ty } → α
  retract_embed : ∀ x, retract (embed x) = x := by has_layout_retract_embed
  embed_retract : ∀ v, embed (retract v) = v := by has_layout_embed_retract

attribute [simp] HasLayout.retract_embed HasLayout.embed_retract

@[simp] theorem HasLayout.embed_valid {α : Type u} [HasLayout α] (x : α) :
    (HasLayout.embed x).val.valid_for (HasLayout.ty α) :=
  (HasLayout.embed x).property

@[expose, inline, simp]
def HasLayout.mkTuple {ts : List MType} (vs : List MVal)
    (h : List.Forall₂ MVal.valid_for vs ts := by simp) :
    { v : MVal // v.valid_for (.tuple ts) } :=
  ⟨.tuple vs, .tuple vs ts h⟩

@[expose, inline, simp]
def HasLayout.mkVariant {ts : List MType} (d : Nat) (v : MVal)
    (hb : d < ts.length := by simp)
    (hv : v.valid_for (ts[d]'hb) := by simp) :
    { v : MVal // v.valid_for (.enum ts) } :=
  ⟨.variant d v, .enum d v ts hb hv⟩

@[expose, inline, simp]
def MVal.valid_for.field {vs : List MVal} {ts : List MType}
    (h : MVal.valid_for (.tuple vs) (.tuple ts)) (i : Fin vs.length) :
    { v : MVal // v.valid_for (ts[i]'(by rw [←h.tuple_len]; exact i.isLt)) } :=
  ⟨vs[i], h.tuple_proj i⟩


@[expose, inline, simp]
def MVal.valid_for.vdata {d : Nat} {v : MVal} {ts : List MType}
    (h : MVal.valid_for (.variant d v) (.enum ts)) :
    { v : MVal // v.valid_for (ts[d]'(h.variant_bound)) } :=
  ⟨v, h.variant_proj⟩

@[expose, inline, simp]
def MVal.valid_for.vfield {d : Nat} {vs : List MVal} {ts vts : List MType}
    (h : MVal.valid_for (.variant d (.tuple vs)) (.enum ts))
    (i : Fin vs.length)
    (hv : ts[d]'(h.variant_bound) = .tuple vts := by rfl) :
    { v : MVal // v.valid_for (vts[i]'(by
        have hp := h.variant_proj; rw [hv] at hp; rw [←hp.tuple_len]; exact i.isLt)) } :=
  ⟨vs[i], (hv ▸ h.variant_proj).tuple_proj i⟩

-- the "special" instances for leaf integers
instance {ty : Std.UScalarTy} : HasLayout (Std.UScalar ty) where
  ty := .int (.unsigned ty)
  embed := λ x ↦ ⟨.int x.val, .int (.unsigned ty) x rfl⟩
  retract := λ | ⟨.int n, _⟩ => ⟨.ofNat ty.numBits n.toNat⟩
  retract_embed := λ x ↦ by cases x; simp
  embed_retract v := match v with
    | ⟨.int n, .int _ vv h_eq⟩ => by simp only [h_eq, IUScalar.val, Std.UScalar.val, BitVec.ofNat_toNat, Int.toNat_natCast, BitVec.setWidth_eq]

instance {ty : Std.IScalarTy} : HasLayout (Std.IScalar ty) where
  ty := .int (.signed ty)
  embed := λ x ↦ ⟨.int x.val, .int (.signed ty) x rfl⟩
  retract := λ | ⟨.int n, _⟩ => ⟨.ofInt ty.numBits n⟩
  retract_embed := λ x ↦ by cases x; simp
  embed_retract v := match v with
    | ⟨.int n, .int _ vv h_eq⟩ => by simp only [h_eq, IUScalar.val, Std.IScalar.val, BitVec.ofInt_toInt]

instance : HasLayout Unit where
  ty := .tuple []
  embed := λ _ ↦ HasLayout.mkTuple []
  retract := λ _ ↦ ()

instance : HasLayout Bool where
  ty := .enum [.tuple [], .tuple []]
  embed := λ | true => HasLayout.mkVariant 0 (.tuple [])
             | false => HasLayout.mkVariant 1 (.tuple [])
  retract := λ | ⟨.variant 0 _, _⟩ => true
               | ⟨.variant 1 _, _⟩ => false

instance {T1 : Type u} {T2 : Type v} [HasLayout T1] [HasLayout T2] : HasLayout (T1 × T2) where
  ty := .tuple [HasLayout.ty T1, HasLayout.ty T2]
  embed := λ (x0, x1) => HasLayout.mkTuple [HasLayout.embed x0, HasLayout.embed x1]
  retract := λ | ⟨.tuple [x0, x1], h⟩ =>
                  (HasLayout.retract (h.field 0), HasLayout.retract (h.field 1))

instance {T1 : Type u} [HasLayout T1] : HasLayout (Option T1) where
  ty := .enum [.tuple [], HasLayout.ty T1]
  embed := λ | .none => HasLayout.mkVariant 0 (.tuple [])
             | .some x => HasLayout.mkVariant 1 (HasLayout.embed x)
  retract := λ | ⟨.variant 0 _, _⟩ => .none
               | ⟨.variant 1 v, h⟩ =>
                  .some (HasLayout.retract ⟨v, h.variant_proj⟩)

inductive Bazinga (T1 : Type u) (T2 : Type v) (T3 : Type w) : Type _ where
| foo1
| foo2 (x : Std.Usize) (y : T1)
| foo3 (x : T2) (y : T3)
| foo4 (b : Bool)

instance {T1 : Type u} {T2 : Type v} {T3 : Type w} [HasLayout T1] [HasLayout T2] [HasLayout T3] : HasLayout (Bazinga T1 T2 T3) where
  ty := .enum [.tuple [], .tuple [HasLayout.ty Std.Usize, HasLayout.ty T1], .tuple [HasLayout.ty T2, HasLayout.ty T3], .tuple [HasLayout.ty Bool]]
  embed := λ | .foo1 => HasLayout.mkVariant 0 (.tuple [])
             | .foo2 x y => HasLayout.mkVariant 1 (.tuple [HasLayout.embed x, HasLayout.embed y])
             | .foo3 x y => HasLayout.mkVariant 2 (.tuple [HasLayout.embed x, HasLayout.embed y])
             | .foo4 x => HasLayout.mkVariant 3 (.tuple [HasLayout.embed x])
  retract := λ | ⟨.variant 0 (.tuple []), _⟩ => .foo1
               | ⟨.variant 1 (.tuple [v0, v1]), h⟩ => .foo2 (HasLayout.retract (h.vfield 0)) (HasLayout.retract (h.vfield 1))
               | ⟨.variant 2 (.tuple [v0, v1]), h⟩ => .foo3 (HasLayout.retract (h.vfield 0)) (HasLayout.retract (h.vfield 1))
               | ⟨.variant 3 (.tuple [v0]), h⟩ => .foo4 (HasLayout.retract (h.vfield 0))

end Aeneas
