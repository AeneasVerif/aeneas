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

end IUScalar

@[expose, simp]
def IUScalarTy.can_repr (ty : IUScalarTy) (z : ℤ) : Prop :=
  ∃ (s : IUScalar ty), s.val = z

/-! ## Machine Types (`MType`) -/

inductive TupleRepr where
| reprRust
| reprC
| reprTransparent
deriving Repr

inductive TupleAlignmentModifier where
| reasonablyAligned -- the default
| packed (n : Nat) (hn : n.isPowerOfTwo)
| aligned (n : Nat) (hn : n.isPowerOfTwo)
deriving Repr

structure TupleFlags where
  repr: TupleRepr
  align: TupleAlignmentModifier
deriving Repr

inductive EnumRepr where
| reprRust
| reprC
| reprC_prim (prim : IUScalarTy)
| reprPrim (prim : IUScalarTy)
deriving Repr
-- we do not handle repr(transparent) on enums for now. Use a struct instead.

inductive EnumAlignmentModifier where
| reasonablyAligned
| aligned (n : Nat) (hn : n.isPowerOfTwo)
deriving Repr

structure EnumFlags where
  repr: EnumRepr
  align: EnumAlignmentModifier
deriving Repr

inductive MType where
  | int (ty : IUScalarTy)
  | tuple (fields : List MType) (f : TupleFlags)
  | enum (variants : List MType) (f : EnumFlags)
deriving Repr

namespace MType

def inhabited : MType → Bool
  | .int _ => true
  | .tuple ts _ => ts.attach.all (λ ⟨t, _⟩ ↦ t.inhabited)
  | .enum vs _ => vs.attach.any (λ ⟨v, _⟩ ↦ v.inhabited)

end MType

/-! ## Machine Values (`MVal`) and Validity (`MVal.valid_for`) -/

inductive MVal where
  | int (i : ℤ)
  | tuple (vs : List MVal)
  | variant (d : Nat) (data : MVal)

namespace MVal

inductive valid_for : (v : MVal) → (ty : MType) → Prop where
  | int : st.can_repr i → valid_for (.int i) (.int st)
  | tuple vs ts : List.Forall₂ valid_for vs ts → valid_for (.tuple vs) (.tuple ts f)
  | enum (dv : Nat) v ts (hb : dv < ts.length) :
      valid_for v ts[dv] →
      valid_for (.variant dv v) (.enum ts f)

end MVal

/-! ## Lemmas and Projections -/

@[simp, grind =] lemma IUScalarTy.numBits_signed (ty : Std.IScalarTy) : (IUScalarTy.signed ty).numBits = ty.numBits := rfl
@[simp, grind =] lemma IUScalarTy.numBits_unsigned (ty : Std.UScalarTy) : (IUScalarTy.unsigned ty).numBits = ty.numBits := rfl
@[simp, grind =] lemma IUScalar.bv_fromBv {ty : IUScalarTy} (bv : BitVec ty.numBits) : (IUScalar.fromBv bv).bv = bv := by
  cases ty <;> rfl

namespace MVal.valid_for

attribute [simp] int tuple enum
attribute [grind ←] int tuple enum

/-! We add some projection functions that allow getting properties out of validity proofs. -/

@[grind →] theorem int_can_repr {z ty} (h : valid_for (.int z) (.int ty)) :
    ty.can_repr z :=
  match h with | .int f => f

@[grind →] theorem tuple_len {vs ts f} (h : valid_for (.tuple vs) (.tuple ts f)) :
    vs.length = ts.length :=
  match h with | .tuple _ _ f => f.length_eq

theorem tuple_proj {vs ts f} (h : valid_for (.tuple vs) (.tuple ts f)) (idx : Nat) (h_idx : idx < vs.length) :
    valid_for vs[idx] (ts[idx]'(by grind)) :=
  match h with | .tuple _ _ f => f.get _ _

grind_pattern tuple_proj => valid_for (.tuple vs) (.tuple ts f), vs[idx]
grind_pattern tuple_proj => valid_for (.tuple vs) (.tuple ts f), ts[idx]

@[grind →] theorem variant_bound {d v ts f} (h : valid_for (.variant d v) (.enum ts f)) :
    d < ts.length :=
  match h with | .enum _ _ _ hb _ => hb

@[grind →] theorem variant_proj {d v ts f} (h : valid_for (.variant d v) (.enum ts f)) :
    v.valid_for (ts[d]'(by grind)) :=
  match h with | .enum _ _ _ _ hv => hv

@[grind →] theorem empty_elim {v : MVal} {i : Nat} {h : i < ([] : List MType).length}
    (_ : valid_for v (([] : List MType)[i]'h)) : False :=
  absurd h (Nat.not_lt_zero i)

/-! Helper functions for projecting valid fields out of valid values. -/
@[expose, inline, simp]
def field {vs : List MVal} {ts : List MType} {f}
    (h : valid_for (.tuple vs) (.tuple ts f)) (i : Nat) (hi : i < vs.length := by simp) :
    { v : MVal // v.valid_for (ts[i]'(by grind)) } :=
  ⟨vs[i], h.tuple_proj i hi⟩

@[expose, inline, simp]
def vdata {d : Nat} {v : MVal} {ts : List MType} {f}
    (h : valid_for (.variant d v) (.enum ts f)) :
    { v : MVal // v.valid_for (ts[d]'(h.variant_bound)) } :=
  ⟨v, h.variant_proj⟩

@[expose, inline, simp]
def vfield {d : Nat} {vs : List MVal} {ts vts : List MType} {f1 f2}
    (h : valid_for (.variant d (.tuple vs)) (.enum ts f1))
    (i : Nat)
    (hv : ts[d]'(h.variant_bound) = .tuple vts f2 := by rfl)
    (hi : i < vs.length := by simp <;> grind) :
    { v : MVal // v.valid_for (vts[i]'(by grind)) } :=
  ⟨vs[i], (hv ▸ h.variant_proj).tuple_proj i hi⟩

end MVal.valid_for

namespace MType

inductive isTuple : MType → Prop where
  | tuple ts : isTuple (.tuple ts ⟨.reprRust, .reasonablyAligned⟩)

attribute [class] isTuple
attribute [instance] isTuple.tuple

end MType

end Aeneas
