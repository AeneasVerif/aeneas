module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Array.Array
public section

namespace Aeneas

/-! ## Scalar Types and Values -/

inductive IUScalarTy where
  | signed (ty : Std.IScalarTy)
  | unsigned (ty : Std.UScalarTy)
deriving Repr

@[expose, implicit_reducible]
def IUScalarTy.numBits (ty : IUScalarTy) : Nat :=
  match ty with
  | .signed ty => ty.numBits
  | .unsigned ty => ty.numBits

@[simp, grind =] lemma IUScalarTy.numBits_signed (ty : Std.IScalarTy) : (IUScalarTy.signed ty).numBits = ty.numBits := rfl
@[simp, grind =] lemma IUScalarTy.numBits_unsigned (ty : Std.UScalarTy) : (IUScalarTy.unsigned ty).numBits = ty.numBits := rfl

@[expose, implicit_reducible]
def IUScalar (ty : IUScalarTy) : Type :=
  match ty with
  | .signed ty => Std.IScalar ty
  | .unsigned ty => Std.UScalar ty

namespace IUScalar

@[expose] def bv {ty} (x : IUScalar ty) : BitVec ty.numBits :=
  match ty with
  | .signed _ => Std.IScalar.bv x
  | .unsigned _ => Std.UScalar.bv x

@[expose] def val {ty} (x : IUScalar ty) : ℤ :=
  match ty with
  | .signed _ => Std.IScalar.val x
  | .unsigned _ => Std.UScalar.val x

@[expose] def fromBv {ty} (bv : BitVec ty.numBits) : IUScalar ty :=
  match ty with
  | .signed _ => ⟨bv⟩
  | .unsigned _ => ⟨bv⟩

@[simp, grind =] lemma bv_fromBv {ty : IUScalarTy} (bv : BitVec ty.numBits) : (fromBv bv).bv = bv := by
  cases ty <;> rfl

end IUScalar

@[expose, simp]
def IUScalarTy.can_repr (ty : IUScalarTy) (z : ℤ) : Prop :=
  ∃ (s : IUScalar ty), s.val = z

/-! ## Machine Types (`MType`) -/

inductive MType where
  | int (ty : IUScalarTy)
  | tuple (fields : List MType)
  | enum (variants : List MType)
deriving Repr

namespace MType

def inhabited : MType → Bool
  | .int _ => true
  | .tuple ts => ts.attach.all (λ ⟨t, _⟩ ↦ t.inhabited)
  | .enum vs => vs.attach.any (λ ⟨v, _⟩ ↦ v.inhabited)

end MType

/-! ## Machine Values (`MVal`) and Validity (`MVal.valid_for`) -/

inductive MVal where
  | int (i : ℤ)
  | tuple (vs : List MVal)
  | variant (d : Nat) (data : MVal)

namespace MVal

inductive valid_for : (v : MVal) → (ty : MType) → Prop where
  | int : st.can_repr i → valid_for (.int i) (.int st)
  | tuple vs ts : List.Forall₂ valid_for vs ts → valid_for (.tuple vs) (.tuple ts)
  | enum (dv : Nat) v ts (hb : dv < ts.length) :
      valid_for v ts[dv] →
      valid_for (.variant dv v) (.enum ts)

namespace valid_for

attribute [simp] int tuple enum
attribute [grind ←] int tuple enum

/-! We add some projection functions that allow getting properties out of validity proofs. -/

@[grind →] theorem int_can_repr {z ty} (h : valid_for (.int z) (.int ty)) :
    ty.can_repr z :=
  match h with | .int f => f

@[grind →] theorem tuple_len {vs ts} (h : valid_for (.tuple vs) (.tuple ts)) :
    vs.length = ts.length :=
  match h with | .tuple _ _ f => f.length_eq

@[grind ←] theorem tuple_proj {vs ts} (h : valid_for (.tuple vs) (.tuple ts)) (idx : Nat) (h_idx : idx < vs.length) :
    valid_for vs[idx] (ts[idx]'(by grind)) :=
  match h with | .tuple _ _ f => f.get _ _

@[grind →] theorem variant_bound {d v ts} (h : valid_for (.variant d v) (.enum ts)) :
    d < ts.length :=
  match h with | .enum _ _ _ hb _ => hb

@[grind →] theorem variant_proj {d v ts} (h : valid_for (.variant d v) (.enum ts)) :
    v.valid_for (ts[d]'(by grind)) :=
  match h with | .enum _ _ _ _ hv => hv

@[grind →] theorem empty_elim {v : MVal} {i : Nat} {h : i < ([] : List MType).length}
    (_ : valid_for v (([] : List MType)[i]'h)) : False :=
  absurd h (Nat.not_lt_zero i)

/-! Helper functions for projecting valid fields out of valid values. -/
@[expose, inline, simp]
def field {vs : List MVal} {ts : List MType}
    (h : valid_for (.tuple vs) (.tuple ts)) (i : Nat) (hi : i < vs.length := by simp) :
    { v : MVal // v.valid_for (ts[i]'(by grind)) } :=
  ⟨vs[i], h.tuple_proj i hi⟩

@[expose, inline, simp]
def vdata {d : Nat} {v : MVal} {ts : List MType}
    (h : valid_for (.variant d v) (.enum ts)) :
    { v : MVal // v.valid_for (ts[d]'(h.variant_bound)) } :=
  ⟨v, h.variant_proj⟩

@[expose, inline, simp]
def vfield {d : Nat} {vs : List MVal} {ts vts : List MType}
    (h : valid_for (.variant d (.tuple vs)) (.enum ts))
    (i : Nat)
    (hi : i < vs.length := by simp)
    (hv : ts[d]'(h.variant_bound) = .tuple vts := by rfl) :
    { v : MVal // v.valid_for (vts[i]'(by grind)) } :=
  ⟨vs[i], (hv ▸ h.variant_proj).tuple_proj i hi⟩

end valid_for
end MVal

namespace MType

inductive isTuple : MType → Prop where
  | tuple ts : isTuple (.tuple ts)

attribute [class] isTuple
attribute [instance] isTuple.tuple
/-! We talk about "Reasonable" types mostly because not all types have a layout, only reasonable ones.
    Notably, we need to rule out enums with a galactic number of variants. -/
inductive Reasonable : MType → Prop where
  | int ty : Reasonable (.int ty)
  | tuple ts :
      (∀ idx (h : idx < ts.length), ts[idx].Reasonable) →
      Reasonable (.tuple ts)
  | enum vs :
      vs.length ≤ Std.Usize.max →
      (∀ idx (h : idx < vs.length), vs[idx].isTuple) →
      (∀ idx (h : idx < vs.length), vs[idx].Reasonable) →
      Reasonable (.enum vs)

attribute [class] Reasonable
attribute [instance] Reasonable.int

class AllReasonable (l : List MType) : Prop where
  out : ∀ idx (h : idx < l.length), l[idx].Reasonable

instance : AllReasonable [] := ⟨λ _ h ↦ nomatch h⟩
instance {x : MType} {xs : List MType} [hx : x.Reasonable] [hxs : AllReasonable xs] :
    AllReasonable (x :: xs) :=
  ⟨λ | 0, _ => hx | n + 1, h => hxs.out n (Nat.lt_of_succ_lt_succ h)⟩

instance {ts : List MType} [h : AllReasonable ts] : (MType.tuple ts).Reasonable :=
  .tuple ts h.out


class AllTuple (l : List MType) : Prop where
  out : ∀ idx (h : idx < l.length), l[idx].isTuple

instance : AllTuple [] := ⟨λ _ h ↦ nomatch h⟩
instance {x : MType} {xs : List MType} [hx : x.isTuple] [hxs : AllTuple xs] :
    AllTuple (x :: xs) :=
  ⟨λ | 0, _ => hx | n + 1, h => hxs.out n (Nat.lt_of_succ_lt_succ h)⟩

-- This instance is better than relying on reduction because that might attempt to reduce (or even get stuck on)
-- the data in this list. But we don't care about the data in the list.
set_option checkBinderAnnotations false in
class inductive ListLengthLe {α : Type _} : List α → Nat → Prop where
  | nil {n} : ListLengthLe [] n
  | cons {x xr n} : [ListLengthLe xr n] → ListLengthLe (x :: xr) (.succ n)

attribute [instance] ListLengthLe.nil ListLengthLe.cons

lemma ListLengthLe.sound [h : ListLengthLe vs n] : vs.length ≤ n := by
  induction h with
  | nil => grind
  | cons ih => grind

instance {vs : List MType}
    [hl : ListLengthLe vs 4294967295] -- this is an astronomical bound
    [ht : AllTuple vs]
    [hr : AllReasonable vs] :
    (MType.enum vs).Reasonable :=
  .enum vs
    (have hl := hl.sound; by rcases System.Platform.numBits_eq with hb | hb <;> simp [Std.Usize.max, Std.Usize.numBits, hb] <;> omega)
    ht.out
    hr.out

end MType

end Aeneas
