/- `core::ptr` -/
module
public import Aeneas.Std.Core.Core
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
public section

open Aeneas SepLogic

namespace Aeneas.Std

/- TODO: this is the definition of `AlignmentEnum` for 64 bit architectures -/
@[rust_type "core::ptr::alignment::AlignmentEnum"]
inductive core.ptr.alignment.AlignmentEnum where
| _Align1Shl0 : core.ptr.alignment.AlignmentEnum
| _Align1Shl1 : core.ptr.alignment.AlignmentEnum
| _Align1Shl2 : core.ptr.alignment.AlignmentEnum
| _Align1Shl3 : core.ptr.alignment.AlignmentEnum
| _Align1Shl4 : core.ptr.alignment.AlignmentEnum
| _Align1Shl5 : core.ptr.alignment.AlignmentEnum
| _Align1Shl6 : core.ptr.alignment.AlignmentEnum
| _Align1Shl7 : core.ptr.alignment.AlignmentEnum
| _Align1Shl8 : core.ptr.alignment.AlignmentEnum
| _Align1Shl9 : core.ptr.alignment.AlignmentEnum
| _Align1Shl10 : core.ptr.alignment.AlignmentEnum
| _Align1Shl11 : core.ptr.alignment.AlignmentEnum
| _Align1Shl12 : core.ptr.alignment.AlignmentEnum
| _Align1Shl13 : core.ptr.alignment.AlignmentEnum
| _Align1Shl14 : core.ptr.alignment.AlignmentEnum
| _Align1Shl15 : core.ptr.alignment.AlignmentEnum
| _Align1Shl16 : core.ptr.alignment.AlignmentEnum
| _Align1Shl17 : core.ptr.alignment.AlignmentEnum
| _Align1Shl18 : core.ptr.alignment.AlignmentEnum
| _Align1Shl19 : core.ptr.alignment.AlignmentEnum
| _Align1Shl20 : core.ptr.alignment.AlignmentEnum
| _Align1Shl21 : core.ptr.alignment.AlignmentEnum
| _Align1Shl22 : core.ptr.alignment.AlignmentEnum
| _Align1Shl23 : core.ptr.alignment.AlignmentEnum
| _Align1Shl24 : core.ptr.alignment.AlignmentEnum
| _Align1Shl25 : core.ptr.alignment.AlignmentEnum
| _Align1Shl26 : core.ptr.alignment.AlignmentEnum
| _Align1Shl27 : core.ptr.alignment.AlignmentEnum
| _Align1Shl28 : core.ptr.alignment.AlignmentEnum
| _Align1Shl29 : core.ptr.alignment.AlignmentEnum
| _Align1Shl30 : core.ptr.alignment.AlignmentEnum
| _Align1Shl31 : core.ptr.alignment.AlignmentEnum
| _Align1Shl32 : core.ptr.alignment.AlignmentEnum
| _Align1Shl33 : core.ptr.alignment.AlignmentEnum
| _Align1Shl34 : core.ptr.alignment.AlignmentEnum
| _Align1Shl35 : core.ptr.alignment.AlignmentEnum
| _Align1Shl36 : core.ptr.alignment.AlignmentEnum
| _Align1Shl37 : core.ptr.alignment.AlignmentEnum
| _Align1Shl38 : core.ptr.alignment.AlignmentEnum
| _Align1Shl39 : core.ptr.alignment.AlignmentEnum
| _Align1Shl40 : core.ptr.alignment.AlignmentEnum
| _Align1Shl41 : core.ptr.alignment.AlignmentEnum
| _Align1Shl42 : core.ptr.alignment.AlignmentEnum
| _Align1Shl43 : core.ptr.alignment.AlignmentEnum
| _Align1Shl44 : core.ptr.alignment.AlignmentEnum
| _Align1Shl45 : core.ptr.alignment.AlignmentEnum
| _Align1Shl46 : core.ptr.alignment.AlignmentEnum
| _Align1Shl47 : core.ptr.alignment.AlignmentEnum
| _Align1Shl48 : core.ptr.alignment.AlignmentEnum
| _Align1Shl49 : core.ptr.alignment.AlignmentEnum
| _Align1Shl50 : core.ptr.alignment.AlignmentEnum
| _Align1Shl51 : core.ptr.alignment.AlignmentEnum
| _Align1Shl52 : core.ptr.alignment.AlignmentEnum
| _Align1Shl53 : core.ptr.alignment.AlignmentEnum
| _Align1Shl54 : core.ptr.alignment.AlignmentEnum
| _Align1Shl55 : core.ptr.alignment.AlignmentEnum
| _Align1Shl56 : core.ptr.alignment.AlignmentEnum
| _Align1Shl57 : core.ptr.alignment.AlignmentEnum
| _Align1Shl58 : core.ptr.alignment.AlignmentEnum
| _Align1Shl59 : core.ptr.alignment.AlignmentEnum
| _Align1Shl60 : core.ptr.alignment.AlignmentEnum
| _Align1Shl61 : core.ptr.alignment.AlignmentEnum
| _Align1Shl62 : core.ptr.alignment.AlignmentEnum
| _Align1Shl63 : core.ptr.alignment.AlignmentEnum

@[reducible, rust_type "core::ptr::alignment::Alignment"]
def core.ptr.alignment.Alignment := core.ptr.alignment.AlignmentEnum

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp

/-! `core::ptr`: the raw-pointer methods (from `core::ptr::mut_ptr` and `core::ptr::const_ptr`) and
the module functions. Each definition with a `rust_fun` pattern models that Rust function, with the
signature Aeneas gives it: a `&mut T` argument is returned updated next to the result. The others
are not Rust functions: `pointsTo`, `pointsToRange` and `pointsToBorrowed` (the `↦`, `↦*` and `↦†`
assertions) fix what specifications state; `InBounds` is the precondition of `add`; the heap-model
operations below (`allocView`, `endView`, `borrow`, `endBorrow` and their range versions) build the
models of the conversions between borrows and raw pointers; and `cast_scalar` is the `as` cast
between scalar raw pointers that the extractor emits by name. -/

namespace RawPtr

/-- `q` owns the `values.length` slots from `q` on. -/
@[expose] def pointsToRange (q : RawPtr T M) (values : List T) : IProp :=
  owns (Heap.array q.loc values)

@[expose] def pointsTo (q : RawPtr T M) (value : T) : IProp :=
  owns (Heap.singleton q value)

/-- `q` owns the `n` borrowed slots from `q` on (borrowed by `borrow`, to be given back by
`endBorrow`). -/
@[expose] def pointsToBorrowed (q : RawPtr T M) : Nat → IProp
  | 0 => emp
  | n + 1 => owns (Heap.borrowedSlot q.loc) ∗ pointsToBorrowed (q.shift 1) n

end RawPtr

instance instPointsToRawPtr {T : Type} {M : Mutability} :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

instance instPointsToRangeRawPtr {T : Type} {M : Mutability} :
    PointsToRange (RawPtr T M) T := ⟨RawPtr.pointsToRange⟩

end Aeneas.Std

namespace Aeneas

scoped notation:50 q:50 " ↦† " n:50 => Std.RawPtr.pointsToBorrowed q n

end Aeneas

namespace Aeneas.Std

open Aeneas
/-- Always fails. TODO: the typed heap cannot read a cell at another scalar type, so casts are not
modelled. -/
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability) [IsScalar T] [IsScalar T']
    (_ : RawPtr T M) : Result (RawPtr T' M') :=
  .fail .undef

/-- `add` stays in bounds: the slots it steps over hold values. -/
def RawPtr.InBounds (q : RawPtr T M) (count : Nat) (h : Heap) : Prop :=
  ∀ i < count, Heap.IsLive h (q.loc.shift i)

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::add"]
def RawPtr.add (q : RawPtr T M) (count : Usize) : Result (RawPtr T M) :=
  Result.guardedModify (fun h => q.InBounds count.val h) fun h _ => (q.shift count.val, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::add"] RawPtr.add

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast_const" -canFail -lift]
def RawPtr.cast_const (q : MutRawPtr T) : ConstRawPtr T :=
  ⟨q.loc⟩

namespace RawPtr

@[rust_fun "core::ptr::const_ptr::{*const @T}::read"]
def read (q : RawPtr T M) : Result T :=
  Result.guardedModify _ (Heap.read q)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read"] read
attribute [rust_fun "core::ptr::read"] read

end RawPtr

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write"]
def MutRawPtr.write (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.guardedModify _ (Heap.write q value)

attribute [rust_fun "core::ptr::write"] MutRawPtr.write

/-! ### Heap-model operations
Aeneas builds its models of Rust's raw-pointer functions (`from_mut`, `as_ptr`, `as_mut_ptr`,
`from_raw_parts`, `from_raw_parts_mut`) from the operations below, which act on the model's heap
directly. -/

/-- Dereferences `q` and marks its slot as borrowed, so that every access to the slot through a raw
pointer fails until the borrow is ended with `endBorrow`. -/
def RawPtr.borrow (q : RawPtr T M) : Result T :=
  Result.guardedModify _ (Heap.borrow q)

def RawPtr.endBorrow (q : RawPtr T M) (value : T) : Result Unit :=
  Result.guardedModify _ (Heap.endBorrow q value)

def RawPtr.borrowRange (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.borrow
    let values ← (q.shift 1).borrowRange n
    .ok (value :: values)

/-- `endBorrow` on the `values.length` slots from `q` on. -/
def RawPtr.endBorrowRange (q : RawPtr T M) : List T → Result Unit
  | [] => .ok ()
  | value :: values => do
    q.endBorrow value
    (q.shift 1).endBorrowRange values

/-- `read` on the `n` slots from `q` on. -/
def RawPtr.readRange (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.read
    let values ← (q.shift 1).readRange n
    .ok (value :: values)

/-- Allocates a raw-pointer view of a place that the functional translation represents as a plain
value, without an address. Used by `from_mut`, `as_ptr` and `as_mut_ptr`. The view is a fresh
allocation holding a copy of `values`, which only `endView` frees (`AllocKind.view`). -/
def RawPtr.allocView (values : List T) : Result (MutRawPtr T) :=
  Result.guardedModify (fun _ => True) fun h _ => h.alloc values .view

def RawPtr.endView (q : RawPtr T M) (count : Nat) : Result Unit :=
  Result.guardedModify _ (Heap.dealloc q count .view)

/-- Back function of `from_mut`: reads the value, with the writes made through the pointer, and
ends the view, so that the pointer can't be used anymore. -/
def core.ptr.end_from_mut (p : MutRawPtr T) : Result T := do
  let value ← p.read
  p.endView 1
  .ok value

/-- The pointer is a view of `r`; the back computation runs when the borrow ends. -/
@[rust_fun "core::ptr::from_mut" (statefulLifetimes := [0])]
def core.ptr.from_mut (r : T) : Result (MutRawPtr T × Result T) :=
  Aeneas.Std.bind (RawPtr.allocView [r]) fun p => .ok (p, core.ptr.end_from_mut p)

open WP

namespace RawPtr

@[simp] theorem shift_zero (q : RawPtr T M) : q.shift 0 = q :=
  RawPtr.ext (by simp)

theorem shift_shift (q : RawPtr T M) (i j : Nat) :
    (q.shift i).shift j = q.shift (i + j) :=
  RawPtr.ext (by simp [Loc.shift_shift])

end RawPtr

theorem RawPtr.pointsTo_eq_singleton (q : RawPtr T M) (value : T) :
    (q ↦ value) = owns (Heap.singleton q value) := rfl

theorem RawPtr.pointsToRange_eq_rangeHeap (q : RawPtr T M) (values : List T) :
    (q ↦* values) = owns (Heap.array q.loc values) := rfl

theorem RawPtr.pointsTo_eq_range (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦* [value]) := by
  rw [RawPtr.pointsTo_eq_singleton, RawPtr.pointsToRange_eq_rangeHeap, Heap.array_singleton,
    Heap.singleton_eq_of_loc (q := q) (r := (⟨q.loc⟩ : MutRawPtr T)) rfl]

namespace RawPtr

theorem pointsToRange_append (q : RawPtr T M) (xs ys : List T) :
    (q ↦* (xs ++ ys)) = iprop(q ↦* xs ∗ (q.shift xs.length) ↦* ys) := by
  rw [pointsToRange_eq_rangeHeap, pointsToRange_eq_rangeHeap, pointsToRange_eq_rangeHeap, loc_shift,
    Heap.array_append q.loc xs ys]
  exact owns_union _ _ (Heap.compatible_array_append q.loc xs ys)

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
  simp only [shift_shift, List.length_singleton]

theorem pointsToRange_cons (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.shift 1) ↦* rest) := by
  rw [show (value :: rest) = [value] ++ rest from rfl,
    pointsToRange_append q [value] rest, ← pointsTo_eq_range]
  simp only [List.length_singleton]

@[simp] theorem pointsToRange_nil (q : RawPtr T M) :
    (q ↦* ([] : List T)) = emp :=
  entails_antisymm (fun _ _ => trivial) fun h _ => by
    rw [pointsToRange_eq_rangeHeap, Heap.array_nil]
    exact Heap.Subheap.of_empty h

@[simp] theorem pointsToBorrowed_zero (q : RawPtr T M) : (q ↦† 0) = emp := rfl

theorem pointsToBorrowed_one (q : RawPtr T M) : (q ↦† 1) = owns (Heap.borrowedSlot q.loc) :=
  sep_emp_r_eq _

theorem pointsToBorrowed_succ (q : RawPtr T M) (n : Nat) :
    (q ↦† (n + 1)) = iprop(q ↦† 1 ∗ (q.shift 1) ↦† n) := by
  rw [pointsToBorrowed_one]
  rfl

end RawPtr

theorem RawPtr.pointsTo_exclusive (q : RawPtr T M) (value₁ value₂ : T) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ := by
  rw [RawPtr.pointsTo_eq_singleton, RawPtr.pointsTo_eq_singleton]
  exact owns_singleton_exclusive q value₁ value₂

namespace RawPtr

theorem contains_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : Heap.IsValid h q :=
  Heap.Subheap.isValid hPointsTo (Heap.isValid_singleton q value)

theorem disjoint_singleton {q r : RawPtr T M} {value₁ value₂ : T} (hNe : q ≠ r) :
    PartialCommMonoid.Compatible (Heap.singleton q value₁) (Heap.singleton r value₂) :=
  Heap.compatible_singleton fun hEq => hNe (RawPtr.ext hEq)

end RawPtr

/-- The right to deallocate the `count` slots at `q` as an allocation of kind `kind`: `q` is at
offset `0` and owns the end marker of its allocation. Only the allocation functions hand it out:
`Global.allocate` (`.global`) and `allocView` (`.view`). Defined directly rather than as
`⌜_⌝ ∗ owns _` so that the separation-logic tactics treat it as one atom. -/
@[expose] def RawPtr.freeable (q : RawPtr T M) (count : Nat := 1) (kind : AllocKind := .global) :
    IProp where
  holds h := q.loc.offset = 0 ∧ Heap.Subheap (Heap.endMarker (q.loc.shift count) kind) h
  up_closed := fun ⟨hOffset, hSub⟩ hExtend => ⟨hOffset, hSub.trans hExtend⟩

theorem RawPtr.freeable_holds {count : Nat} {kind : AllocKind} (q : RawPtr T M) (h : Heap) :
    q.freeable count kind h ↔
      q.loc.offset = 0 ∧ Heap.Subheap (Heap.endMarker (q.loc.shift count) kind) h :=
  Iff.rfl

@[simp] theorem RawPtr.freeable_cast_const (q : MutRawPtr T) (count : Nat) (kind : AllocKind) :
    q.cast_const.freeable count kind = q.freeable count kind := by
  unfold RawPtr.cast_const; rfl

/-- A fresh allocation hands out its values and the right to deallocate it. -/
theorem Heap.alloc.spec (values : List T) (kind : AllocKind) :
    ispec emp (Result.guardedModify (fun _ => True) fun h _ => h.alloc values kind)
      (fun q => q ↦* values ∗ q.freeable values.length kind) := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.allocation (Heap.freshLoc (h ∪ frame)) values kind) (h ∪ frame) :=
    Heap.compatible_freshLoc _ _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.allocation (Heap.freshLoc (h ∪ frame)) values kind) h frame).mpr
        ⟨hCompatible, hFresh⟩
  refine ⟨trivial, _, hFreshFrame, ?_, ?_⟩
  · rw [Heap.alloc_eq]
    exact (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm
  · rw [Heap.alloc_eq]
    have hAllocation := Heap.Subheap.union_left (h₂ := h) hFreshH
    rw [Heap.allocation_eq] at hAllocation
    have hSplit : (owns (Heap.array (Heap.freshLoc (h ∪ frame)) values) ∗
        owns (Heap.endMarker ((Heap.freshLoc (h ∪ frame)).shift values.length) kind))
          (Heap.allocation (Heap.freshLoc (h ∪ frame)) values kind ∪ h) := by
      rw [← owns_union _ _ (Heap.compatible_array_endMarker _ _ _), Heap.allocation_eq]
      exact hAllocation
    exact sep_mono (entails_refl _)
      (fun h' hEnd => (RawPtr.freeable_holds _ h').mpr ⟨Heap.freshLoc_offset _, hEnd⟩) _ hSplit

/-- Deallocating needs the values and the right to deallocate them: without it, `q` could be an
interior pointer, or point to an allocation of another kind. -/
theorem Heap.dealloc.spec (q : RawPtr T M) (values : List T) (kind : AllocKind) :
    ispec (q ↦* values ∗ q.freeable values.length kind)
      (Result.guardedModify _ (Heap.dealloc q values.length kind)) (fun _ => emp) := by
  apply ispec_guardedModify
  intro h hPre frame hCompatible
  have hRange : Heap.Subheap (Heap.array q.loc values) h := sep_elim_right _ _ h hPre
  obtain ⟨hOffset, hEnd⟩ := (RawPtr.freeable_holds q h).mp (sep_elim_left _ _ h hPre)
  have hDealloc : Heap.CanDealloc h q values.length kind :=
    Heap.canDealloc_iff.mpr ⟨hOffset, fun _ hi => hRange.isLive (Heap.isLive_array hi),
      Heap.Subheap.isEndMarker hEnd⟩
  exact ⟨Heap.canDealloc_union_left hDealloc, (h.dealloc q values.length kind hDealloc).2,
    Heap.compatible_dealloc_left hCompatible hDealloc,
    congrArg Prod.snd (Heap.dealloc_union_left hDealloc), trivial⟩

@[step]
theorem RawPtr.allocView.spec (values : List T) :
    ⦃ emp ⦄ RawPtr.allocView values ⦃ p => p ↦* values ∗ p.freeable values.length .view⦄ :=
  Heap.alloc.spec values .view

@[step]
theorem RawPtr.endView.spec (q : RawPtr T M) (values : List T) (count : Nat)
    (hCount : values.length = count) :
    ⦃ q ↦* values ∗ q.freeable count .view ⦄ q.endView count ⦃ emp⦄ := by
  subst hCount
  exact Heap.dealloc.spec q values .view

namespace RawPtr

@[simp] theorem addr_cast_const (q : MutRawPtr T) : q.cast_const.loc = q.loc := by
  unfold RawPtr.cast_const; rfl

@[simp] theorem pointsTo_cast_const (q : MutRawPtr T) (value : T) :
    (q.cast_const ↦ value) = (q ↦ value) := by
  rw [pointsTo_eq_singleton, pointsTo_eq_singleton,
    Heap.singleton_eq_of_loc (q := q.cast_const) (r := q) rfl]

@[simp] theorem pointsToRange_cast_const (q : MutRawPtr T) (values : List T) :
    (q.cast_const ↦* values) = (q ↦* values) := by
  unfold RawPtr.cast_const; rfl

@[step]
theorem read.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ q ↦ value⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Subheap.union_left hCompatible)
  have hContains := contains_of_pointsTo hPointsToFrame
  refine ⟨hContains, h, hCompatible, by rw [Heap.read_snd], ?_⟩
  exact (sep_pure_l _ _ h).mpr ⟨Heap.read_of_subheap hPointsToFrame hContains, hPointsTo⟩

end RawPtr

@[step]
theorem MutRawPtr.write.spec (q : MutRawPtr T) (oldValue newValue : T) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃ q ↦ newValue⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hPointsTo
  have hContainsSlot := Heap.isValid_singleton q oldValue
  have hContains : Heap.IsValid (Heap.singleton q oldValue ∪ rest) q :=
    Heap.isValid_union_left hContainsSlot
  refine ⟨Heap.isValid_union_left hContains,
    (Heap.write q newValue _ hContains).2,
    Heap.compatible_write_left hCompatible hContains, ?_, ?_⟩
  · exact congrArg Prod.snd (Heap.write_union_left (h₂ := frame) q newValue hContains)
  · have hCompatibleNew :
        PartialCommMonoid.Compatible (Heap.singleton q newValue) rest := by
      have hUpdated := Heap.compatible_write_left (value := newValue)
        hCompatibleRest hContainsSlot
      rwa [Heap.write_singleton] at hUpdated
    rw [show hContains = Heap.isValid_union_left hContainsSlot from
      Subsingleton.elim _ _, Heap.write_union_left q newValue hContainsSlot]
    simp only [Prod.map_snd, Heap.write_singleton]
    exact Heap.Subheap.union_left hCompatibleNew

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
  refine ⟨fun i hi => ?_, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨rfl, hRange⟩⟩
  exact Heap.Subheap.isLive ((show Heap.Subheap (Heap.array q.loc values) h from hRange).trans
    (Heap.Subheap.union_left hCompatible)) (Heap.isLive_array (by omega))

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

theorem MutRawPtr.write.spec_head (q : MutRawPtr T) (values : List T) (value : T)
    (h : 0 < values.length) :
    ⦃ q ↦* values ⦄ q.write value ⦃ q ↦* values.set 0 value⦄ := by
  simpa using MutRawPtr.write.spec_range q values 0 value h

namespace RawPtr

@[step]
theorem borrow.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.borrow ⦃ result => ⌜result = value⌝ ∗ q ↦† 1⦄ := by
  rw [pointsToBorrowed_one]
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Subheap.union_left hCompatible)
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hPointsTo
  have hSlot := Heap.isValid_singleton q value
  have hValid : Heap.IsValid (Heap.singleton q value ∪ rest) q := Heap.isValid_union_left hSlot
  refine ⟨Heap.isValid_union_left hValid, (Heap.borrow q _ hValid).2,
    Heap.compatible_borrow_left hCompatible hValid, ?_, ?_⟩
  · exact congrArg Prod.snd (Heap.borrow_union_left (h₂ := frame) q hValid)
  · have hBorrowedRest : PartialCommMonoid.Compatible (Heap.borrowedSlot q.loc) rest := by
      have hBorrowed := Heap.compatible_borrow_left hCompatibleRest hSlot
      rwa [Heap.borrow_singleton] at hBorrowed
    refine (sep_pure_l _ _ _).mpr
      ⟨(Heap.borrow_fst _).trans (Heap.read_of_subheap hPointsToFrame _), ?_⟩
    rw [show hValid = Heap.isValid_union_left hSlot from Subsingleton.elim _ _,
      Heap.borrow_union_left q hSlot]
    simp only [Prod.map_snd, Heap.borrow_singleton]
    exact Heap.Subheap.union_left hBorrowedRest

@[step]
theorem endBorrow.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦† 1 ⦄ q.endBorrow value ⦃ q ↦ value⦄ := by
  rw [pointsToBorrowed_one]
  apply ispec_guardedModify
  intro h hBorrowedSub frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hBorrowedSub
  have hSlot := Heap.isBorrowed_borrowedSlot q.loc
  have hBorrowed : Heap.IsBorrowed (Heap.borrowedSlot q.loc ∪ rest) q.loc :=
    Heap.isBorrowed_union_left hSlot
  refine ⟨Heap.isBorrowed_union_left hBorrowed, (Heap.endBorrow q value _ hBorrowed).2,
    Heap.compatible_endBorrow_left hCompatible hBorrowed, ?_, ?_⟩
  · exact congrArg Prod.snd (Heap.endBorrow_union_left (h₂ := frame) q value hBorrowed)
  · have hLiveRest : PartialCommMonoid.Compatible (Heap.singleton q value) rest := by
      have hLive := Heap.compatible_endBorrow_left (value := value) (q := q) hCompatibleRest hSlot
      rwa [Heap.endBorrow_borrowedSlot] at hLive
    show Heap.Subheap _ _
    rw [show hBorrowed = Heap.isBorrowed_union_left hSlot from Subsingleton.elim _ _,
      Heap.endBorrow_union_left q value hSlot]
    simp only [Prod.map_snd, Heap.endBorrow_borrowedSlot]
    exact Heap.Subheap.union_left hLiveRest

@[step]
theorem borrowRange.spec (q : RawPtr T M) (values : List T) :
    ⦃ q ↦* values ⦄ q.borrowRange values.length
      ⦃ result => ⌜result = values⌝ ∗ q ↦† values.length⦄ := by
  induction values generalizing q with
  | nil => simp [borrowRange]
  | cons value values ih =>
    rw [pointsToRange_cons, List.length_cons, pointsToBorrowed_succ, borrowRange]
    apply WP.ispec_bind (borrow.spec q value)
    · iframe
    · intro v
      apply WP.ispec_bind (ih (q.shift 1))
      · iframe
      · intro vs
        apply (WP.ispec_ok _).2
        iframe

@[step]
theorem endBorrowRange.spec (q : RawPtr T M) (values : List T) :
    ⦃ q ↦† values.length ⦄ q.endBorrowRange values ⦃ q ↦* values⦄ := by
  induction values generalizing q with
  | nil => simp [endBorrowRange]
  | cons value values ih =>
    rw [pointsToRange_cons, List.length_cons, pointsToBorrowed_succ, endBorrowRange]
    apply WP.ispec_bind (endBorrow.spec q value)
    · iframe
    · intro _
      apply WP.ispec_mono (ih (q.shift 1)) <;> iframe

/-- `endBorrowRange.spec` with the number of borrowed slots given separately. -/
theorem endBorrowRange.spec_len (q : RawPtr T M) (values : List T) (n : Nat)
    (h : values.length = n) :
    ⦃ q ↦† n ⦄ q.endBorrowRange values ⦃ q ↦* values⦄ := by
  subst h
  exact endBorrowRange.spec q values

@[step]
theorem readRange.spec (q : RawPtr T M) (values : List T) :
    ⦃ q ↦* values ⦄ q.readRange values.length
      ⦃ result => ⌜result = values⌝ ∗ q ↦* values⦄ := by
  induction values generalizing q with
  | nil => simp [readRange]
  | cons value values ih =>
    rw [pointsToRange_cons, List.length_cons, readRange]
    apply WP.ispec_bind (read.spec q value)
    · iframe
    · intro v
      apply WP.ispec_bind (ih (q.shift 1))
      · iframe
      · intro vs
        apply (WP.ispec_ok _).2
        iframe

end RawPtr

@[step]
theorem Result.require.spec {p : Prop} (hp : p) : ⦃ emp ⦄ Result.require p ⦃ emp⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  exact ⟨hp, h, hCompatible, rfl, trivial⟩

@[step]
theorem core.ptr.from_mut.spec (value : T) :
    ⦃ emp ⦄ core.ptr.from_mut value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_mut q⌝ ∗ q ↦ value ∗ q.freeable 1 .view⦄ := by
  unfold core.ptr.from_mut
  apply WP.ispec_bind (RawPtr.allocView.spec [value])
  · iframe
  · intro q
    apply (ispec_ok _).2
    simp only [uncurry_apply_pair, ← RawPtr.pointsTo_eq_range, List.length_singleton]
    iframe

@[step]
theorem core.ptr.end_from_mut.spec (q : MutRawPtr T) (value : T) :
    ⦃ q ↦ value ∗ q.freeable 1 .view ⦄ core.ptr.end_from_mut q
      ⦃ result => ⌜result = value⌝⦄ := by
  unfold core.ptr.end_from_mut
  apply WP.ispec_bind (RawPtr.read.spec q value)
  · iframe
  · intro result
    rw [SepLogic.sep_assoc_eq, WP.ispec_ipure]
    rintro rfl
    apply WP.ispec_bind (RawPtr.endView.spec q [result] 1 rfl)
    · rw [← RawPtr.pointsTo_eq_range]
      iframe
    · intro _
      apply (WP.ispec_ok _).2
      iframe

end Aeneas.Std
