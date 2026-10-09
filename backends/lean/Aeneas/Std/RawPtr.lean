module
public import Aeneas.Std.Delab
public import Aeneas.Std.Heap
public import Aeneas.SepLogic.IProp
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.SliceDef
public import Aeneas.Data.List.List
public import Aeneas.Std.WP
public import Aeneas.Std.Primitives
public import Aeneas.SepLogic.Lemmas
public import Aeneas.SepLogic.Delab
public import Aeneas.SepLogic.Tactic.IFrame
public import Aeneas.SepLogic.Tactic.IIntro
public import Aeneas.SepLogic.Tactic.IRewrite
public import Aeneas.SepLogic.Tactic.ISimp
public import Aeneas.Tactic.Step.Init
@[expose] public section

open Aeneas SepLogic

namespace Aeneas.Std

/-! ### START Trusted definitions

Every executable definition below models a Rust function (see its `rust_fun` pattern), with the
signature Aeneas gives that function: `Box<T>` is `T`, and a `&mut T` argument is returned updated
next to the result. The exceptions are `RawPtr.materialize`, the allocation primitive behind
them, and `RawPtr.cast_scalar`, the `as` cast between raw pointers, which always fails. -/

inductive Mutability where
| Mut | Const

/-- A Rust raw pointer: an allocation identifier and an offset into it. -/
structure RawPtr (T : Type) (M : Mutability) where
  base : AllocId
  offset : Nat
  deriving Inhabited, DecidableEq

abbrev MutRawPtr (T : Type) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type) := RawPtr T .Const

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab RawPtr]
meta def delabRawPtr : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``RawPtr 2)
  let name ← match e.appArg! with
    | .const ``Mutability.Mut _ => pure ``MutRawPtr
    | .const ``Mutability.Const _ => pure ``ConstRawPtr
    | _ => failure
  let t ← withNaryArg 0 delab
  `($(mkIdent (← unresolveNameGlobal name)) $t)

namespace RawPtr

def addr (q : RawPtr T M) : Loc := (q.base, q.offset)

/-- `q` moved `i` slots forward, for specifications. Programs use `add`. -/
def shift (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.base, q.offset + i⟩

def retype (q : RawPtr T M) : RawPtr U M' :=
  ⟨q.base, q.offset⟩

/-- `q` owns the `values.length` slots from `q` on. -/
def pointsToRange (q : RawPtr T M) (values : List T) : IProp :=
  owns (Heap.rangeHeap q.addr values)

def pointsTo (q : RawPtr T M) (value : T) : IProp :=
  owns (Heap.singleton q.addr value)

end RawPtr

instance instPointsToRawPtr {T : Type} {M : Mutability} :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

notation:50 q:50 " ↦* " values:50 => RawPtr.pointsToRange q values

/-- Not a Rust function: stores `values` in fresh slots. -/
def RawPtr.materialize (values : List T) : Result (RawPtr T M) :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (⟨(Heap.freshLoc h).1, (Heap.freshLoc h).2⟩, Heap.freshHeap h values)

/-- `add` stays in bounds. -/
def RawPtr.InBounds (q : RawPtr T M) (count : Nat) (h : Heap) : Prop :=
  ∀ i < count, ∃ α, Heap.contains h α (q.addr.add i)

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::add"]
def RawPtr.add (q : RawPtr T M) (count : Usize) : Result (RawPtr T M) :=
  Result.guardedModify (fun h => q.InBounds count.val h) fun h _ => (q.shift count.val, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::add"] RawPtr.add

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast_const" -canFail -lift]
def RawPtr.cast_const (q : MutRawPtr T) : ConstRawPtr T :=
  q.retype

namespace RawPtr

structure Readable (q : RawPtr T M) (h : Heap) : Prop where
  contains : Heap.contains h T q.addr

@[rust_fun "core::ptr::const_ptr::{*const @T}::read"]
def read (q : RawPtr T M) : Result T :=
  Result.guardedModify (fun h => q.Readable h) fun h hReadable =>
    (Heap.read q.addr h hReadable.contains, h)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read"] read
attribute [rust_fun "core::ptr::read"] read

end RawPtr

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write"]
def MutRawPtr.write (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h T q.addr) fun h hContains =>
    ((), Heap.update q.addr value h hContains)

attribute [rust_fun "core::ptr::write"] MutRawPtr.write

@[rust_fun "alloc::boxed::{Box<@T>}::into_raw"]
def alloc.boxed.Box.into_raw (b : T) : Result (MutRawPtr T) :=
  RawPtr.materialize [b]

/-- Moves the value out and frees its slot. -/
@[rust_fun "alloc::boxed::{Box<@T>}::from_raw"]
def alloc.boxed.Box.from_raw (p : MutRawPtr T) : Result T :=
  Result.guardedModify (fun h => Heap.contains h T p.addr) fun h hContains =>
    (Heap.read p.addr h hContains, Heap.free p.addr h hContains)

/-- The pointer points to a fresh copy of `r`, and `r` is returned unchanged. -/
@[rust_fun "core::ptr::from_mut"]
def core.ptr.from_mut (r : T) : Result (MutRawPtr T × T) := do
  let p ← RawPtr.materialize [r]
  pure (p, r)

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

-- TODO: the typed heap cannot read a cell at another scalar type, so casts are not modelled
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability) [IsScalar T] [IsScalar T']
    (_ : RawPtr T M) : Result (RawPtr T' M') :=
  .fail .undef

/-! ### END Trusted definitions -/

namespace RawPtr

def singleton (q : RawPtr T M) (value : T) : Heap :=
  Heap.singleton q.addr value

def contains (h : Heap) (q : RawPtr T M) : Prop :=
  Heap.contains h T q.addr

end RawPtr

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp

open WP

namespace RawPtr

@[simp] theorem base_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).base = q.base := rfl

@[simp] theorem offset_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).offset = q.offset + i := rfl

@[simp] theorem shift_zero (q : RawPtr T M) : q.shift 0 = q := rfl

@[simp] theorem cast_const_eq_retype (q : MutRawPtr T) : q.cast_const = q.retype := rfl

@[simp] theorem base_retype (q : RawPtr T M) : (q.retype : RawPtr U M').base = q.base := rfl

@[simp] theorem offset_retype (q : RawPtr T M) :
    (q.retype : RawPtr U M').offset = q.offset := rfl

@[simp] theorem addr_retype (q : RawPtr T M) : (q.retype : RawPtr U M').addr = q.addr := rfl

theorem addr_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).addr = q.addr.add i := rfl

theorem shift_shift (q : RawPtr T M) (i j : Nat) :
    (q.shift i).shift j = q.shift (i + j) := by
  simp [shift, Nat.add_assoc]

end RawPtr

theorem RawPtr.pointsTo_eq_singleton (q : RawPtr T M) (value : T) :
    (q ↦ value) = owns (Heap.singleton q.addr value) := rfl

theorem RawPtr.pointsTo_eq_range (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦* [value]) := by
  rw [RawPtr.pointsTo_eq_singleton, RawPtr.pointsToRange, Heap.rangeHeap_singleton]

@[simp] theorem RawPtr.pointsTo_retype (q : RawPtr T M) (value : T) :
    ((q.retype : RawPtr T M') ↦ value) = (q ↦ value) := rfl

@[simp] theorem RawPtr.pointsToRange_retype (q : RawPtr T M) (values : List T) :
    ((q.retype : RawPtr T M') ↦* values) = (q ↦* values) := rfl

namespace RawPtr

theorem pointsToRange_append (q : RawPtr T M) (xs ys : List T) :
    (q ↦* (xs ++ ys)) = iprop(q ↦* xs ∗ (q.shift xs.length) ↦* ys) := by
  rw [pointsToRange, pointsToRange, pointsToRange, addr_shift,
    Heap.rangeHeap_append q.addr xs ys]
  exact owns_union _ _ (Heap.compatible_rangeHeap_append q.addr xs ys)

theorem pointsToRange_split (q : RawPtr T M) (values : List T) (i : Nat) :
    (q ↦* values) =
      iprop(q ↦* values.take i ∗ (q.shift (values.take i).length) ↦* values.drop i) := by
  conv_lhs => rw [← List.take_append_drop i values]
  exact pointsToRange_append q (values.take i) (values.drop i)

theorem pointsToRange_eq_take_get_drop {q : RawPtr T M} {values : List T} {i : Nat}
    (hIndex : i < values.length) :
    (q ↦* values) =
      iprop(q ↦* values.take i ∗
        ((q.shift i) ↦ values[i] ∗ (q.shift (i + 1)) ↦* values.drop (i + 1))) := by
  have hTake : (values.take i).length = i := by simp; omega
  have hSplit := pointsToRange_split q values i
  rw [hTake] at hSplit
  rw [hSplit, List.drop_eq_getElem_cons hIndex,
    show values[i] :: values.drop (i + 1)
      = [values[i]] ++ values.drop (i + 1) from rfl,
    pointsToRange_append (q.shift i) [values[i]] (values.drop (i + 1)),
    ← pointsTo_eq_range]
  rfl

theorem pointsToRange_cons (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.shift 1) ↦* rest) := by
  rw [show (value :: rest) = [value] ++ rest from rfl,
    pointsToRange_append q [value] rest, ← pointsTo_eq_range]
  rfl

@[simp] theorem pointsToRange_nil (q : RawPtr T M) :
    (q ↦* ([] : List T)) = emp :=
  entails_antisymm (fun _ _ => trivial) (fun h _ => Heap.Sub.of_empty h)

end RawPtr

theorem RawPtr.pointsTo_exclusive (q : RawPtr T M) (value₁ value₂ : T) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ := by
  rw [RawPtr.pointsTo_eq_singleton, RawPtr.pointsTo_eq_singleton]
  exact owns_singleton_exclusive q.addr value₁ value₂

namespace RawPtr

@[simp]
theorem not_contains_empty (q : RawPtr T M) :
    ¬ RawPtr.contains (∅ : Heap) q :=
  Heap.not_contains_empty q.addr

theorem contains_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : RawPtr.contains h q :=
  Heap.Sub.contains hPointsTo (Heap.contains_singleton q.addr value)

theorem addr_injective {q r : RawPtr T M} (hEq : q.addr = r.addr) : q = r := by
  cases q
  cases r
  have hBase := congrArg Prod.fst hEq
  have hOffset := congrArg Prod.snd hEq
  simp only [RawPtr.addr] at hBase hOffset
  simp_all

theorem disjoint_singleton {q r : RawPtr T M} {value₁ value₂ : T} (hNe : q ≠ r) :
    PartialCommMonoid.Compatible (q.singleton value₁) (r.singleton value₂) :=
  Heap.disjoint_singleton fun hEq => hNe (addr_injective hEq)

end RawPtr

@[step]
theorem RawPtr.materialize.spec (values : List T) :
    ⦃ emp ⦄ RawPtr.materialize (M := M) values
      ⦃ p => p ↦* values⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.allocation (Heap.freshLoc (h ∪ frame)) values) (h ∪ frame) :=
    Heap.compatible_freshLoc _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.allocation (Heap.freshLoc (h ∪ frame)) values) h frame).mpr
        ⟨hCompatible, hFresh⟩
  exact ⟨trivial, _, hFreshFrame,
    (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm,
    (Heap.sub_allocation _ _).trans (Heap.Sub.union_left hFreshH)⟩

@[step]
theorem alloc.boxed.Box.into_raw.spec (value : T) :
    ⦃ emp ⦄ alloc.boxed.Box.into_raw value ⦃ q => q ↦ value⦄ := by
  simpa only [alloc.boxed.Box.into_raw, RawPtr.pointsTo_eq_range] using
    RawPtr.materialize.spec (M := .Mut) [value]

namespace RawPtr

theorem readable_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : q.Readable h :=
  ⟨contains_of_pointsTo hPointsTo⟩

@[step]
theorem read.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ q ↦ value⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  have hReadable : q.Readable (h ∪ frame) :=
    readable_of_pointsTo hPointsToFrame
  refine ⟨hReadable, h, hCompatible, rfl, ?_⟩
  exact (sep_pure_l _ _ h).mpr
    ⟨Heap.read_of_sub hPointsToFrame hReadable.contains, hPointsTo⟩

end RawPtr

@[step]
theorem MutRawPtr.write.spec (q : MutRawPtr T) (oldValue newValue : T) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃ q ↦ newValue⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hPointsTo
  have hContainsSlot := Heap.contains_singleton q.addr oldValue
  have hContains : Heap.contains (Heap.singleton q.addr oldValue ∪ rest) T q.addr :=
    Heap.contains_union_left hContainsSlot
  refine ⟨Heap.contains_union_left hContains,
    Heap.update q.addr newValue _ hContains,
    Heap.disjoint_update_left hCompatible hContains, ?_, ?_⟩
  · simpa only [show Heap.contains_union_left hContains =
        Heap.contains_union_left (h₂ := frame) hContains from rfl] using
      Heap.update_union_left q.addr newValue hContains
  · have hCompatibleNew :
        PartialCommMonoid.Compatible (Heap.singleton q.addr newValue) rest := by
      have hUpdated := Heap.disjoint_update_left (value := newValue)
        hCompatibleRest hContainsSlot
      rwa [Heap.update_singleton] at hUpdated
    rw [show hContains = Heap.contains_union_left hContainsSlot from
      Subsingleton.elim _ _, Heap.update_union_left q.addr newValue hContainsSlot,
      Heap.update_singleton]
    exact Heap.Sub.union_left hCompatibleNew

@[step]
theorem alloc.boxed.Box.from_raw.spec {value : T} (q : MutRawPtr T) :
    ⦃ q ↦ value ⦄ alloc.boxed.Box.from_raw q
      ⦃ result => ⌜result = value⌝⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : Heap.contains h T q.addr := RawPtr.contains_of_pointsTo hPointsTo
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  refine ⟨Heap.contains_union_left hContains, Heap.free q.addr h hContains,
    Heap.disjoint_free_left hCompatible hContains, ?_, ?_⟩
  · simpa only [show Heap.contains_union_left hContains =
        Heap.contains_union_left (h₂ := frame) hContains from rfl] using
      Heap.free_union_left q.addr hCompatible hContains
  · exact Heap.read_of_sub hPointsToFrame _

namespace RawPtr

theorem take_set (values : List T) (i : Nat) (value : T) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set,
    if_neg (show ¬ i = n by omega)]

theorem drop_set (values : List T) (i : Nat) (value : T) :
    (values.set i value).drop (i + 1) = values.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_drop, List.getElem_set,
    if_neg (show ¬ i = i + 1 + n by omega)]

theorem read.spec_range (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ (q.shift i).read
      ⦃ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read.spec (q.shift i) values[i]) <;> iframe

theorem read.spec_frame (q : RawPtr T M) (value : T) (H : IProp) :
    ⦃ q ↦ value ∗ H ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ := by
  apply WP.ispec_mono (read.spec q value) <;> iframe

@[step]
theorem add.spec (q : RawPtr T M) (values : List T) (count : Usize)
    (hCount : count.val ≤ values.length) :
    ⦃ q ↦* values ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦* values⦄ := by
  apply ispec_guardedModify
  intro h hRange frame hCompatible
  refine ⟨fun i hi => ⟨T, ?_⟩, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨rfl, hRange⟩⟩
  exact Heap.Sub.contains ((show Heap.Sub (Heap.rangeHeap q.addr values) h from hRange).trans
    (Heap.Sub.union_left hCompatible)) (Heap.contains_rangeHeap (by omega))

end RawPtr

theorem MutRawPtr.write.spec_range (q : MutRawPtr T) (values : List T)
    (i : Nat) (value : T) (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ MutRawPtr.write (q.shift i) value
      ⦃ q ↦* values.set i value⦄ := by
  rw [RawPtr.pointsToRange_eq_take_get_drop hIndex,
    RawPtr.pointsToRange_eq_take_get_drop
      (show i < (values.set i value).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set, List.getElem_set_self]
  apply WP.ispec_mono (MutRawPtr.write.spec (q.shift i) values[i] value) <;> iframe

@[step]
theorem core.ptr.from_mut.spec (value : T) :
    ⦃ emp ⦄ core.ptr.from_mut value ⦃ (q, back) => ⌜back = value⌝ ∗ q ↦ value⦄ := by
  unfold core.ptr.from_mut
  apply WP.ispec_bind (alloc.boxed.Box.into_raw.spec value)
  · iframe
  · intro q
    apply (ispec_ok _).2
    iframe

end Aeneas.Std
