module
public import Aeneas.Data.Layout.GaloisConnection

@[expose] public section

namespace Aeneas

@[simp, grind =]
def EnumFlags.maxVariants (f : EnumFlags) : Nat :=
  match f.repr with
  | .reprRust | .reprC => Std.Usize.max
  | .reprC_prim prim | .reprPrim prim => 2 ^ prim.numBits

@[simp, reducible]
def IUScalarTy.minMaxVariants : IUScalarTy → Nat
  | .unsigned .U8 | .signed .I8 => 256
  | .unsigned .U16 | .signed .I16 => 65536
  | _ => 4294967295

@[simp, reducible]
def EnumFlags.minMaxVariants (f : EnumFlags) : Nat :=
  match f.repr with
  | .reprRust | .reprC => 4294967295
  | .reprC_prim prim | .reprPrim prim => prim.minMaxVariants

lemma EnumFlags.minMaxVariants_le_maxVariants (f : EnumFlags) : f.minMaxVariants ≤ f.maxVariants := by
  rcases f with ⟨repr, align⟩
  cases repr with
  | reprRust | reprC =>
    rcases System.Platform.numBits_eq with hb | hb <;>
      simp [minMaxVariants, maxVariants, Std.Usize.max, Std.Usize.numBits, hb]
  | reprC_prim prim | reprPrim prim =>
    rcases prim with ⟨ty⟩ | ⟨ty⟩ <;> cases ty <;>
      rcases System.Platform.numBits_eq with hb | hb <;>
      simp [minMaxVariants, IUScalarTy.minMaxVariants, maxVariants, IUScalarTy.numBits, Std.UScalarTy.numBits, Std.IScalarTy.numBits, hb]

namespace MType

class TupleFlagsReasonable (f : TupleFlags) : Prop where
  out : f.repr = .reprTransparent → f.align = .reasonablyAligned

instance {f} : TupleFlagsReasonable ⟨.reprC, f⟩ := by constructor; simp
instance {f} : TupleFlagsReasonable ⟨.reprRust, f⟩ := by constructor; simp
instance : TupleFlagsReasonable ⟨.reprTransparent, .reasonablyAligned⟩ := by constructor; simp

/-! We talk about "Reasonable" types mostly because not all types have a layout, only reasonable ones.
    Notably, we need to rule out enums with a galactic number of variants. -/
inductive Reasonable : MType → Prop where
  | int ty : Reasonable (.int ty)
  | tuple ts f :
      (∀ idx (h : idx < ts.length), ts[idx].Reasonable) →
      TupleFlagsReasonable f →
      Reasonable (.tuple ts f)
  | enum vs f :
      vs.length ≤ f.maxVariants →
      (∀ idx (h : idx < vs.length), vs[idx].isTuple) →
      (∀ idx (h : idx < vs.length), vs[idx].Reasonable) →
      Reasonable (.enum vs f)

attribute [class] Reasonable
attribute [instance] Reasonable.int

class AllReasonable {α : Type} (l : List α) (f : α → MType) : Prop where
  out : ∀ idx (h : idx < l.length), (f l[idx]).Reasonable

instance {α : Type} {f : α → MType} : AllReasonable [] f := ⟨λ _ h ↦ nomatch h⟩
instance {α : Type} {x : α} {xs : List α} {f : α → MType} [hx : (f x).Reasonable] [hxs : AllReasonable xs f] :
    AllReasonable (x :: xs) f :=
  ⟨λ | 0, _ => hx | n + 1, h => hxs.out n (Nat.lt_of_succ_lt_succ h)⟩

instance {α β : Type} {f1 : α → β} {f2 : β → MType} {xs : List α} [h : AllReasonable xs (λ x ↦ f2 (f1 x))] :
    MType.AllReasonable (xs.map f1) f2 := by
  constructor; simp; apply h.out

instance {ts : List MType} {f} [h : AllReasonable ts id] [fr : TupleFlagsReasonable f] : (MType.tuple ts f).Reasonable :=
  .tuple ts f h.out fr

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

instance {α β : Type} {f : α → β} {xs : List α} n [h : ListLengthLe xs n] : ListLengthLe (xs.map f) n := by
  induction h with
  | nil => constructor
  | cons ih => constructor

lemma ListLengthLe.sound [h : ListLengthLe vs n] : vs.length ≤ n := by
  induction h with
  | nil => grind
  | cons ih => grind

instance {vs : List MType} {f}
    [hl : ListLengthLe vs f.minMaxVariants]
    [ht : AllTuple vs]
    [hr : AllReasonable vs id] :
    (MType.enum vs f).Reasonable :=
  .enum vs f
    (Nat.le_trans hl.sound f.minMaxVariants_le_maxVariants)
    ht.out
    hr.out

end MType

namespace Layout.ReprC

theorem mk_reasonablyAligned (ty : MType) [hr : ty.Reasonable] : (mk ty).ReasonablyAligned := by
  induction hr <;> grind [mk, Layout.ReasonablyAligned.int]

end Layout.ReprC

end Aeneas
