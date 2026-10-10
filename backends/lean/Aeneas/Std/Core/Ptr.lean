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
are not Rust functions: `pointsToCell`, `pointsToCells`, `pointsTo`, `pointsToRange` and
`pointsToBorrowed` (the `↦?`, `↦*?`, `↦`, `↦*` and `↦†` assertions) fix what specifications state;
`InBounds` is the precondition of `add`; `Readable` is the precondition of `read`; the heap-model
operations below (`alloc`, `allocView`, `endView`, `borrow`, `endBorrow` and their range versions)
build the models of the conversions between borrows and raw pointers; `null`, `LiveBox` and
`NonZeroSized` define `eq` and `ne`, which model `==` and `!=` on raw pointers; and `cast_scalar` is
the `as` cast between scalar raw pointers that the extractor emits by name.

The heap is typed: a pointer to `T` reads and writes cells of type `Pointee.Cell T`, which is `T`
itself except for `MaybeUninit<U>`, whose cells are the (possibly uninitialized) cells of `U`.
Every access checks the type of the cell, so that casting a pointer (`<*mut T>::cast`) is safe: an
access at a type which does not match the cell fails. -/

/-- How the values of type `T` are stored in the heap: a value is a cell of type `Cell`, which may
be uninitialized (`none`). `ofCell` gives back the value stored in a cell, if any: reading an
uninitialized cell fails unless `T` can represent uninitialized memory (`MaybeUninit`).

The cells of `T` must have the memory representation of `T`: this is what makes pointer casts
between types with the same cells meaningful.

Limitation: the instance is resolved where a definition is elaborated, so generic code (with a
type parameter `T`) always uses `Pointee.default`, whose cells have type `T`. Instantiated with
`T := MaybeUninit U`, such code accesses cells of type `MaybeUninit U`, while the concrete
functions on `MaybeUninit U` (and the slices, boxes and pointers created from them) use cells of
type `U`: the accesses of the generic code to those cells always fail (this is sound, but such
programs can not be verified). -/
class Pointee (T : Type) where
  Cell : Type
  toCell : T → Option Cell
  ofCell : Option Cell → Option T
  ofCell_toCell (value : T) : ofCell (toCell value) = some value

/-- By default, the cells of `T` hold initialized values of type `T`. -/
@[expose] instance (priority := low) Pointee.default {T : Type} : Pointee T where
  Cell := T
  toCell := some
  ofCell := id
  ofCell_toCell _ := rfl

@[simp] theorem Pointee.toCell_default {T : Type} (value : T) :
    @Pointee.toCell T Pointee.default value = some value := rfl

@[simp] theorem Pointee.ofCell_default {T : Type} (content : Option T) :
    @Pointee.ofCell T Pointee.default content = content := rfl

namespace RawPtr

/-- `q` as a pointer to the cells of its pointee. -/
@[expose, reducible] def cellPtr [Pointee T] (q : RawPtr T M) : RawPtr (Pointee.Cell T) M :=
  ⟨q.loc⟩

/-- `q` owns a cell holding `content` (uninitialized if `content = none`). -/
@[expose] def pointsToCell [Pointee T] (q : RawPtr T M) (content : Option (Pointee.Cell T)) :
    IProp :=
  owns (Heap.cell q.cellPtr content)

/-- `q` owns the `contents.length` cells from `q` on. -/
@[expose] def pointsToCells [Pointee T] (q : RawPtr T M)
    (contents : List (Option (Pointee.Cell T))) : IProp :=
  owns (Heap.array q.loc contents)

@[expose] def pointsTo [Pointee T] (q : RawPtr T M) (value : T) : IProp :=
  q.pointsToCell (Pointee.toCell value)

/-- `q` owns the `values.length` slots from `q` on. -/
@[expose] def pointsToRange [Pointee T] (q : RawPtr T M) (values : List T) : IProp :=
  q.pointsToCells (values.map Pointee.toCell)

/-- `q` owns the `n` borrowed slots from `q` on (borrowed by `borrow`, to be given back by
`endBorrow`). -/
@[expose] def pointsToBorrowed (q : RawPtr T M) : Nat → IProp
  | 0 => emp
  | n + 1 => owns (Heap.borrowedSlot q.loc) ∗ pointsToBorrowed (q.shift 1) n

end RawPtr

instance instPointsToRawPtr {T : Type} [Pointee T] {M : Mutability} :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

instance instPointsToRangeRawPtr {T : Type} [Pointee T] {M : Mutability} :
    PointsToRange (RawPtr T M) T := ⟨RawPtr.pointsToRange⟩

end Aeneas.Std

namespace Aeneas

scoped notation:50 q:50 " ↦† " n:50 => Std.RawPtr.pointsToBorrowed q n
scoped notation:50 q:50 " ↦? " content:50 => Std.RawPtr.pointsToCell q content
scoped notation:50 q:50 " ↦*? " contents:50 => Std.RawPtr.pointsToCells q contents

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

@[expose, rust_fun "core::ptr::mut_ptr::{*mut @T}::cast_const" -canFail -lift]
def RawPtr.cast_const (q : MutRawPtr T) : ConstRawPtr T :=
  ⟨q.loc⟩

/-- Changes the pointee type. The accesses through the new pointer check that the cells have the
type of the cells of the new pointee (see `Pointee`), so a cast is only useful between types with
the same cells, such as `MaybeUninit<T>` and `T`. -/
@[expose, rust_fun "core::ptr::mut_ptr::{*mut @T}::cast" -canFail -lift]
def RawPtr.cast {T : Type _} {M : Mutability} (U : Type _) (q : RawPtr T M) : RawPtr U M :=
  ⟨q.loc⟩

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::cast" -canFail -lift] RawPtr.cast

namespace RawPtr

/-- `q` points to a live cell of the type of the cells of its pointee, holding a value of the
pointee. -/
structure Readable [Pointee T] (q : RawPtr T M) (h : Heap) : Prop where
  valid : Heap.IsValid h q.cellPtr
  init : (Pointee.ofCell (h.read q.cellPtr valid).1).isSome

/-- The value `q` points to. -/
def get [Pointee T] (q : RawPtr T M) (h : Heap) (hReadable : q.Readable h) : T :=
  (Pointee.ofCell (h.read q.cellPtr hReadable.valid).1).get hReadable.init

@[rust_fun "core::ptr::const_ptr::{*const @T}::read"]
def read [Pointee T] (q : RawPtr T M) : Result T :=
  Result.guardedModify q.Readable fun h hReadable => (q.get h hReadable, h)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read"] read
attribute [rust_fun "core::ptr::read"] read

end RawPtr

/-- Writing initializes the cell, which may be uninitialized. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write"]
def MutRawPtr.write [Pointee T] (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.guardedModify _ (Heap.write q.cellPtr (Pointee.toCell value))

attribute [rust_fun "core::ptr::write"] MutRawPtr.write

/-! ### Heap-model operations
Aeneas builds its models of Rust's raw-pointer functions (`from_mut`, `as_ptr`, `as_mut_ptr`,
`from_raw_parts`, `from_raw_parts_mut`) from the operations below, which act on the model's heap
directly. -/

/-- Dereferences `q` and marks its slot as borrowed, so that every access to the slot through a raw
pointer fails until the borrow is ended with `endBorrow`. -/
def RawPtr.borrow [Pointee T] (q : RawPtr T M) : Result T :=
  Result.guardedModify q.Readable fun h hReadable =>
    (q.get h hReadable, (h.borrow q.cellPtr hReadable.valid).2)

def RawPtr.endBorrow [Pointee T] (q : RawPtr T M) (value : T) : Result Unit :=
  Result.guardedModify _ (Heap.endBorrow q.cellPtr (Pointee.toCell value))

def RawPtr.borrowRange [Pointee T] (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.borrow
    let values ← (q.shift 1).borrowRange n
    .ok (value :: values)

/-- `endBorrow` on the `values.length` slots from `q` on. -/
def RawPtr.endBorrowRange [Pointee T] (q : RawPtr T M) : List T → Result Unit
  | [] => .ok ()
  | value :: values => do
    q.endBorrow value
    (q.shift 1).endBorrowRange values

/-- `read` on the `n` slots from `q` on. -/
def RawPtr.readRange [Pointee T] (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.read
    let values ← (q.shift 1).readRange n
    .ok (value :: values)

/-- A fresh allocation of kind `kind` holding `values`. Fresh memory is mutable in Rust. -/
def RawPtr.alloc [Pointee T] (values : List T) (kind : AllocKind) : Result (MutRawPtr T) :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (⟨Heap.freshLoc h⟩, (h.alloc (values.map Pointee.toCell) kind).2)

/-- Allocates a raw-pointer view of a place that the functional translation represents as a plain
value, without an address. Used by `from_mut`, `as_ptr` and `as_mut_ptr`. The view is a fresh
allocation holding a copy of `values`, which only `endView` frees (`AllocKind.view`). -/
def RawPtr.allocView [Pointee T] (values : List T) : Result (MutRawPtr T) :=
  RawPtr.alloc values .view

def RawPtr.endView (q : RawPtr T M) (count : Nat) : Result Unit :=
  Result.guardedModify _ (Heap.dealloc q count .view)

/-- Back function of `from_mut`: reads the value, with the writes made through the pointer, and
ends the view, so that the pointer can't be used anymore. -/
def core.ptr.end_from_mut [Pointee T] (p : MutRawPtr T) : Result T := do
  let value ← p.read
  p.endView 1
  .ok value

/-- The pointer is a view of `r`; the back computation runs when the borrow ends. -/
@[rust_fun "core::ptr::from_mut" (statefulLifetimes := [0])]
def core.ptr.from_mut [Pointee T] (r : T) : Result (MutRawPtr T × Result T) :=
  Aeneas.Std.bind (RawPtr.allocView [r]) fun p => .ok (p, core.ptr.end_from_mut p)

/-- `&mut *p`: the value is moved out of its slot, which is borrowed so that the other accesses to
it fail while the borrow is live, and the slot gets back the final value of the borrow when the
borrow ends (`statefulLifetimes`). The extraction translates the borrows of places behind raw
pointers (`&mut (*p).f`) to this function. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::as_mut_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_mut_unchecked [Pointee T] (p : MutRawPtr T) : Result (T × (T → Result Unit)) :=
  Aeneas.Std.bind p.borrow fun value => .ok (value, p.endBorrow)

/-- `&*p`: like `as_mut_unchecked`, the value is moved out while the borrow is live, so that
writing through another pointer fails (this is conservative: reading through another pointer
also fails), and given back unchanged when the borrow ends. -/
@[rust_fun "core::ptr::const_ptr::{*const @T}::as_ref_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_ref_unchecked [Pointee T] (p : RawPtr T M) : Result (T × Result Unit) :=
  Aeneas.Std.bind p.borrow fun value => .ok (value, p.endBorrow value)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::as_ref_unchecked" (statefulLifetimes := [0])]
  RawPtr.as_ref_unchecked

/-- The null pointer. The allocation `0` is never allocated (see `Heap.freshAllocId`): the
pointers to it can not be dereferenced. -/
@[expose] def RawPtr.null : RawPtr T M := ⟨⟨0, 0⟩⟩

@[rust_fun "core::ptr::null" -canFail -lift]
def core.ptr.null (T : Type _) : ConstRawPtr T := RawPtr.null

@[rust_fun "core::ptr::null_mut" -canFail -lift]
def core.ptr.null_mut (T : Type _) : MutRawPtr T := RawPtr.null

/-- `q` points to the live cell of a one-cell allocation of the global allocator (a box, see
`Box::into_raw`). -/
def RawPtr.LiveBox (q : RawPtr T M) (h : Heap) : Prop :=
  Heap.IsLive h q.loc ∧ Heap.IsEndMarker h (q.loc.shift 1) .global

/-- `nonZero T = true` if the Rust type modelled by `T` is known not to be zero-sized. Different
slots of the same allocation, or live allocations, then have different addresses. By default (in
particular in generic code, and for `MaybeUninit<()>`, whose Lean model has two values but which is
zero-sized) the type may be zero-sized. The extraction derives the instances of the structures
from their fields (see `RawPtr.eq`); adding an instance is an assumption. -/
class NonZeroSized (T : Type) where
  nonZero : Bool

instance (priority := low) NonZeroSized.default : NonZeroSized T := ⟨false⟩
instance : NonZeroSized (UScalar ty) := ⟨true⟩
instance : NonZeroSized (IScalar ty) := ⟨true⟩
instance : NonZeroSized Bool := ⟨true⟩
instance : NonZeroSized Char := ⟨true⟩
instance : NonZeroSized (RawPtr T M) := ⟨true⟩
instance [NonZeroSized T] : NonZeroSized (Option T) := ⟨NonZeroSized.nonZero T⟩

/-- Pointer comparison (`==` on raw pointers, `NonNull`). The model does not know the addresses:
two pointers are equal if they are the same. Otherwise they are different if they point to
different slots of the same allocation, or to two live boxes (live allocations do not overlap),
and the pointee is not zero-sized (`NonZeroSized`). In the other cases the comparison fails: in
particular, the pointers obtained from borrows (`from_mut`, `as_ptr`, `NonNull::from`...) point to
fresh copies of the borrowed values, whose actual addresses are those of the borrowed values, and
freed allocations may share their addresses with new ones. -/
def RawPtr.eq [NonZeroSized T] (p q : RawPtr T M) : Result Bool :=
  if p.loc = q.loc then .ok true
  else Result.guardedModify
    (fun h => NonZeroSized.nonZero T ∧ (p.loc.allocId = q.loc.allocId ∨ p.LiveBox h ∧ q.LiveBox h))
    fun h _ => (false, h)

/-- `!=` on pointers (see `RawPtr.eq`). -/
def RawPtr.ne [NonZeroSized T] (p q : RawPtr T M) : Result Bool :=
  Aeneas.Std.bind (p.eq q) fun b => .ok (!b)

open WP

namespace RawPtr

@[simp] theorem shift_zero (q : RawPtr T M) : q.shift 0 = q :=
  RawPtr.ext (by simp)

theorem shift_shift (q : RawPtr T M) (i j : Nat) :
    (q.shift i).shift j = q.shift (i + j) :=
  RawPtr.ext (by simp [Loc.shift_shift])

@[simp] theorem loc_cast (q : RawPtr T M) (U : Type _) : (q.cast U).loc = q.loc := rfl

@[simp] theorem cast_cast (q : RawPtr T M) (U V : Type _) : (q.cast U).cast V = q.cast V := rfl

@[simp] theorem cast_self (q : RawPtr T M) : q.cast T = q := rfl

@[simp] theorem shift_cast (q : RawPtr T M) (U : Type _) (i : Nat) :
    (q.cast U).shift i = (q.shift i).cast U :=
  RawPtr.ext (by simp)

@[simp] theorem loc_cast_const (q : MutRawPtr T) : q.cast_const.loc = q.loc := rfl

end RawPtr

section PointsTo

variable {T : Type} [Pointee T] {M : Mutability}

namespace RawPtr

@[simp] theorem loc_cellPtr (q : RawPtr T M) : q.cellPtr.loc = q.loc := rfl

theorem pointsTo_eq (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦? Pointee.toCell value) := rfl

theorem pointsToRange_eq (q : RawPtr T M) (values : List T) :
    (q ↦* values) = (q ↦*? values.map Pointee.toCell) := rfl

theorem pointsToCell_eq_cell (q : RawPtr T M) (content : Option (Pointee.Cell T)) :
    (q ↦? content) = owns (Heap.cell q.cellPtr content) := rfl

theorem pointsToCells_eq_array (q : RawPtr T M) (contents : List (Option (Pointee.Cell T))) :
    (q ↦*? contents) = owns (Heap.array q.loc contents) := rfl

theorem pointsToCell_eq_cells (q : RawPtr T M) (content : Option (Pointee.Cell T)) :
    (q ↦? content) = (q ↦*? [content]) := by
  rw [pointsToCell_eq_cell, pointsToCells_eq_array, Heap.array_singleton,
    Heap.cell_eq_of_loc (q := q.cellPtr) (r := (⟨q.loc⟩ : MutRawPtr (Pointee.Cell T))) rfl]

theorem pointsTo_eq_range (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦* [value]) :=
  pointsToCell_eq_cells q _


@[simp] theorem pointsToRange_cast_const (q : MutRawPtr T) (values : List T) :
    (q.cast_const ↦* values) = (q ↦* values) := rfl

@[simp] theorem pointsToCell_cast_const (q : MutRawPtr T) (content : Option (Pointee.Cell T)) :
    (q.cast_const ↦? content) = (q ↦? content) := by
  rw [pointsToCell_eq_cell, pointsToCell_eq_cell]
  exact congrArg owns (Heap.cell_eq_of_loc (q := q.cast_const.cellPtr) (r := q.cellPtr) rfl _)

@[simp] theorem pointsTo_cast_const (q : MutRawPtr T) (value : T) :
    (q.cast_const ↦ value) = (q ↦ value) :=
  pointsToCell_cast_const q _

@[simp] theorem pointsToCells_cast_const (q : MutRawPtr T)
    (contents : List (Option (Pointee.Cell T))) :
    (q.cast_const ↦*? contents) = (q ↦*? contents) := rfl

theorem pointsToCells_append (q : RawPtr T M) (xs ys : List (Option (Pointee.Cell T))) :
    (q ↦*? (xs ++ ys)) = iprop(q ↦*? xs ∗ (q.shift xs.length) ↦*? ys) := by
  rw [pointsToCells_eq_array, pointsToCells_eq_array, pointsToCells_eq_array, loc_shift,
    Heap.array_append q.loc xs ys]
  exact owns_union _ _ (Heap.compatible_array_append q.loc xs ys)

theorem pointsToCells_split (q : RawPtr T M) (contents : List (Option (Pointee.Cell T)))
    (i : Nat) :
    (q ↦*? contents) =
      iprop(q ↦*? contents.take i ∗ (q.shift (contents.take i).length) ↦*? contents.drop i) := by
  conv_lhs => rw [← List.take_append_drop i contents]
  exact pointsToCells_append q (contents.take i) (contents.drop i)

theorem pointsToCells_eq_take_get_drop {q : RawPtr T M}
    {contents : List (Option (Pointee.Cell T))} {i : Nat} (hIndex : i < contents.length) :
    (q ↦*? contents) =
      iprop(q ↦*? contents.take i ∗
        ((q.shift i) ↦? contents[i] ∗ (q.shift (i + 1)) ↦*? contents.drop (i + 1))) := by
  have hTake : (contents.take i).length = i := by simp; omega
  have hSplit := pointsToCells_split q contents i
  rw [hTake] at hSplit
  rw [hSplit, List.drop_eq_getElem_cons hIndex,
    show contents[i] :: contents.drop (i + 1)
      = [contents[i]] ++ contents.drop (i + 1) from rfl,
    pointsToCells_append (q.shift i) [contents[i]] (contents.drop (i + 1)),
    ← pointsToCell_eq_cells]
  simp only [shift_shift, List.length_singleton]

theorem pointsToCells_cons (q : RawPtr T M) (content : Option (Pointee.Cell T))
    (rest : List (Option (Pointee.Cell T))) :
    (q ↦*? (content :: rest)) = iprop(q ↦? content ∗ (q.shift 1) ↦*? rest) := by
  rw [show (content :: rest) = [content] ++ rest from rfl,
    pointsToCells_append q [content] rest, ← pointsToCell_eq_cells]
  simp only [List.length_singleton]

@[simp] theorem pointsToCells_nil (q : RawPtr T M) :
    (q ↦*? ([] : List (Option (Pointee.Cell T)))) = emp :=
  entails_antisymm (fun _ _ => trivial) fun h _ => by
    rw [pointsToCells_eq_array, Heap.array_nil]
    exact Heap.Subheap.of_empty h

theorem pointsToRange_append (q : RawPtr T M) (xs ys : List T) :
    (q ↦* (xs ++ ys)) = iprop(q ↦* xs ∗ (q.shift xs.length) ↦* ys) := by
  rw [pointsToRange_eq, List.map_append, pointsToCells_append, List.length_map]
  rfl

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
  rw [pointsToRange_eq, pointsToCells_eq_take_get_drop (by simpa using hIndex)]
  simp only [← List.map_take, ← List.map_drop, List.getElem_map]
  rfl

theorem pointsToRange_cons (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.shift 1) ↦* rest) := by
  rw [pointsToRange_eq, List.map_cons, pointsToCells_cons]
  rfl

@[simp] theorem pointsToRange_nil (q : RawPtr T M) :
    (q ↦* ([] : List T)) = emp :=
  pointsToCells_nil q

end RawPtr

end PointsTo

namespace RawPtr

@[simp] theorem pointsToBorrowed_zero (q : RawPtr T M) : (q ↦† 0) = emp := rfl

theorem pointsToBorrowed_one (q : RawPtr T M) : (q ↦† 1) = owns (Heap.borrowedSlot q.loc) :=
  sep_emp_r_eq _

theorem pointsToBorrowed_succ (q : RawPtr T M) (n : Nat) :
    (q ↦† (n + 1)) = iprop(q ↦† 1 ∗ (q.shift 1) ↦† n) := by
  rw [pointsToBorrowed_one]
  rfl

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
    q.cast_const.freeable count kind = q.freeable count kind := rfl

@[simp] theorem RawPtr.freeable_cast (q : RawPtr T M) (U : Type _) (count : Nat)
    (kind : AllocKind) : (q.cast U).freeable count kind = q.freeable count kind := rfl

/-- `q` owns the freed slot at `q`: the memory at `q` was deallocated. -/
@[expose] def RawPtr.freed (q : RawPtr T M) : IProp :=
  owns (Heap.freedSlot q.loc)

section

variable {T : Type} [Pointee T] {M : Mutability}

theorem RawPtr.pointsToCell_exclusive (q : RawPtr T M)
    (content₁ content₂ : Option (Pointee.Cell T)) :
    q ↦? content₁ ∗ q ↦? content₂ ⊢ ⌜False⌝ :=
  owns_cell_exclusive q.cellPtr content₁ content₂

theorem RawPtr.pointsTo_exclusive (q : RawPtr T M) (value₁ value₂ : T) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ :=
  RawPtr.pointsToCell_exclusive q _ _

namespace RawPtr

theorem isValid_of_pointsToCell {q : RawPtr T M} {content : Option (Pointee.Cell T)} {h : Heap}
    (hPointsTo : (q ↦? content) h) : Heap.IsValid h q.cellPtr :=
  Heap.Subheap.isValid hPointsTo (Heap.isValid_cell q.cellPtr content)

theorem get_eq {q : RawPtr T M} {h : Heap} {value : T} (hReadable : q.Readable h)
    (hValue : Pointee.ofCell (h.read q.cellPtr hReadable.valid).1 = some value) :
    q.get h hReadable = value :=
  Option.some.inj ((Option.some_get _).trans hValue)

theorem readable_of_pointsToCell {q : RawPtr T M} {content : Option (Pointee.Cell T)} {value : T}
    {h : Heap} (hPointsTo : (q ↦? content) h) (hValue : Pointee.ofCell content = some value) :
    q.Readable h :=
  have hValid := isValid_of_pointsToCell hPointsTo
  ⟨hValid, by rw [Heap.read_of_subheap hPointsTo hValid, hValue]; rfl⟩

theorem get_of_pointsToCell {q : RawPtr T M} {content : Option (Pointee.Cell T)} {value : T}
    {h : Heap} (hPointsTo : (q ↦? content) h) (hValue : Pointee.ofCell content = some value)
    (hReadable : q.Readable h) : q.get h hReadable = value :=
  get_eq hReadable (by rw [Heap.read_of_subheap hPointsTo, hValue])

theorem readable_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : q.Readable h :=
  readable_of_pointsToCell hPointsTo (Pointee.ofCell_toCell value)

theorem get_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) (hReadable : q.Readable h) : q.get h hReadable = value :=
  get_of_pointsToCell hPointsTo (Pointee.ofCell_toCell value) hReadable

end RawPtr

/-- A fresh allocation hands out its values and the right to deallocate it. -/
theorem RawPtr.alloc.spec (values : List T) (kind : AllocKind) :
    ⦃ emp ⦄ RawPtr.alloc values kind ⦃ q => q ↦* values ∗ q.freeable values.length kind⦄ := by
  unfold RawPtr.alloc
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.allocation (Heap.freshLoc (h ∪ frame)) (values.map Pointee.toCell) kind)
        (h ∪ frame) :=
    Heap.compatible_freshLoc _ _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.allocation (Heap.freshLoc (h ∪ frame)) (values.map Pointee.toCell) kind) h frame).mpr
        ⟨hCompatible, hFresh⟩
  refine ⟨trivial, _, hFreshFrame, ?_, ?_⟩
  · rw [Heap.alloc_eq]
    exact (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm
  · rw [Heap.alloc_eq]
    have hAllocation := Heap.Subheap.union_left (h₂ := h) hFreshH
    rw [Heap.allocation_eq] at hAllocation
    have hSplit : (owns (Heap.array (Heap.freshLoc (h ∪ frame)) (values.map Pointee.toCell)) ∗
        owns (Heap.endMarker
          ((Heap.freshLoc (h ∪ frame)).shift (values.map Pointee.toCell).length) kind))
          (Heap.allocation (Heap.freshLoc (h ∪ frame)) (values.map Pointee.toCell) kind ∪ h) := by
      rw [← owns_union _ _ (Heap.compatible_array_endMarker _ _ _), Heap.allocation_eq]
      exact hAllocation
    rw [List.length_map] at hSplit
    exact sep_mono (entails_refl _)
      (fun h' hEnd => (RawPtr.freeable_holds _ h').mpr ⟨Heap.freshLoc_offset _, hEnd⟩) _ hSplit

/-- Deallocating needs the values and the right to deallocate them: without it, `q` could be an
interior pointer, or point to an allocation of another kind. The slot at `q` is then freed. -/
theorem Heap.dealloc.spec_freed (q : RawPtr T M) (contents : List (Option (Pointee.Cell T)))
    (kind : AllocKind) :
    ispec (q ↦*? contents ∗ q.freeable contents.length kind)
      (Result.guardedModify _ (Heap.dealloc q contents.length kind)) (fun _ => q.freed) := by
  apply ispec_guardedModify
  intro h hPre frame hCompatible
  have hRange : Heap.Subheap (Heap.array q.loc contents) h := sep_elim_right _ _ h hPre
  obtain ⟨hOffset, hEnd⟩ := (RawPtr.freeable_holds q h).mp (sep_elim_left _ _ h hPre)
  have hDealloc : Heap.CanDealloc h q contents.length kind :=
    Heap.canDealloc_iff.mpr ⟨hOffset, fun _ hi => hRange.isLive (Heap.isLive_array hi),
      Heap.Subheap.isEndMarker hEnd⟩
  exact ⟨Heap.canDealloc_union_left hDealloc, (h.dealloc q contents.length kind hDealloc).2,
    Heap.compatible_dealloc_left hCompatible hDealloc,
    congrArg Prod.snd (Heap.dealloc_union_left hDealloc),
    Heap.subheap_freedSlot (by simpa using Heap.isFreed_dealloc hDealloc (Nat.zero_le _))⟩

theorem Heap.dealloc.spec (q : RawPtr T M) (contents : List (Option (Pointee.Cell T)))
    (kind : AllocKind) :
    ispec (q ↦*? contents ∗ q.freeable contents.length kind)
      (Result.guardedModify _ (Heap.dealloc q contents.length kind)) (fun _ => emp) :=
  WP.ispec_mono (Heap.dealloc.spec_freed q contents kind) (entails_of_eq (sep_emp_r_eq _).symm)
    (by iframe)

@[step]
theorem RawPtr.allocView.spec (values : List T) :
    ⦃ emp ⦄ RawPtr.allocView values ⦃ p => p ↦* values ∗ p.freeable values.length .view⦄ :=
  RawPtr.alloc.spec values .view

/-- Ending a view needs its cells, initialized or not. -/
theorem RawPtr.endView.spec_cells (q : RawPtr T M) (contents : List (Option (Pointee.Cell T)))
    (count : Nat) (hCount : contents.length = count) :
    ⦃ q ↦*? contents ∗ q.freeable count .view ⦄ q.endView count ⦃ emp⦄ := by
  subst hCount
  exact Heap.dealloc.spec q contents .view

@[step]
theorem RawPtr.endView.spec (q : RawPtr T M) (values : List T) (count : Nat)
    (hCount : values.length = count) :
    ⦃ q ↦* values ∗ q.freeable count .view ⦄ q.endView count ⦃ emp⦄ :=
  RawPtr.endView.spec_cells q (values.map Pointee.toCell) count (by simpa using hCount)

namespace RawPtr

/-- Reading needs the cell to hold a value of the pointee (`hValue`). -/
theorem read.spec_cell (q : RawPtr T M) (content : Option (Pointee.Cell T)) (value : T)
    (hValue : Pointee.ofCell content = some value) :
    ⦃ q ↦? content ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ q ↦? content⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦? content) (h ∪ frame) :=
    (q ↦? content).up_closed hPointsTo (Heap.Subheap.union_left hCompatible)
  have hReadable := readable_of_pointsToCell hPointsToFrame hValue
  exact ⟨hReadable, h, hCompatible, rfl,
    (sep_pure_l _ _ h).mpr ⟨get_of_pointsToCell hPointsToFrame hValue hReadable, hPointsTo⟩⟩

@[step]
theorem read.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ q ↦ value⦄ :=
  read.spec_cell q _ value (Pointee.ofCell_toCell value)

end RawPtr

/-- Writing needs a live cell of the right type, initialized or not. -/
theorem MutRawPtr.write.spec_cell (q : MutRawPtr T) (content : Option (Pointee.Cell T))
    (newValue : T) :
    ⦃ q ↦? content ⦄ q.write newValue ⦃ q ↦ newValue⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hPointsTo
  have hContainsSlot := Heap.isValid_cell q.cellPtr content
  have hContains : Heap.IsValid (Heap.cell q.cellPtr content ∪ rest) q.cellPtr :=
    Heap.isValid_union_left hContainsSlot
  refine ⟨Heap.isValid_union_left hContains,
    (Heap.write q.cellPtr (Pointee.toCell newValue) _ hContains).2,
    Heap.compatible_write_left hCompatible hContains, ?_, ?_⟩
  · exact congrArg Prod.snd
      (Heap.write_union_left (h₂ := frame) q.cellPtr (Pointee.toCell newValue) hContains)
  · have hCompatibleNew :
        PartialCommMonoid.Compatible (Heap.cell q.cellPtr (Pointee.toCell newValue)) rest := by
      have hUpdated := Heap.compatible_write_left (value := Pointee.toCell newValue)
        hCompatibleRest hContainsSlot
      rwa [Heap.write_cell] at hUpdated
    rw [show hContains = Heap.isValid_union_left hContainsSlot from
      Subsingleton.elim _ _, Heap.write_union_left q.cellPtr _ hContainsSlot]
    simp only [Prod.map_snd, Heap.write_cell]
    exact Heap.Subheap.union_left hCompatibleNew

@[step]
theorem MutRawPtr.write.spec (q : MutRawPtr T) (oldValue newValue : T) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃ q ↦ newValue⦄ :=
  MutRawPtr.write.spec_cell q _ newValue

namespace RawPtr

theorem take_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set,
    if_neg (show ¬ i = n by omega)]

theorem drop_set (values : List α) (i : Nat) (value : α) :
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

/-- `add` stays in bounds of the range of cells `q` owns, initialized or not. -/
theorem add.spec_cells (q : RawPtr T M) (contents : List (Option (Pointee.Cell T)))
    (count : Usize) (hCount : count.val ≤ contents.length) :
    ⦃ q ↦*? contents ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦*? contents⦄ := by
  apply ispec_guardedModify
  intro h hRange frame hCompatible
  refine ⟨fun i hi => ?_, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨rfl, hRange⟩⟩
  exact Heap.Subheap.isLive ((show Heap.Subheap (Heap.array q.loc contents) h from hRange).trans
    (Heap.Subheap.union_left hCompatible)) (Heap.isLive_array (by omega))

@[step]
theorem add.spec (q : RawPtr T M) (values : List T) (count : Usize)
    (hCount : count.val ≤ values.length) :
    ⦃ q ↦* values ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦* values⦄ :=
  add.spec_cells q _ count (by simpa using hCount)

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

/-- `write.spec_range` on a range of cells, some of which may be uninitialized. -/
theorem MutRawPtr.write.spec_cells (q : MutRawPtr T) (contents : List (Option (Pointee.Cell T)))
    (i : Nat) (value : T) (hIndex : i < contents.length) :
    ⦃ q ↦*? contents ⦄ MutRawPtr.write (q.shift i) value
      ⦃ q ↦*? contents.set i (Pointee.toCell value)⦄ := by
  rw [RawPtr.pointsToCells_eq_take_get_drop hIndex,
    RawPtr.pointsToCells_eq_take_get_drop
      (show i < (contents.set i (Pointee.toCell value)).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set, List.getElem_set_self]
  apply WP.ispec_mono (MutRawPtr.write.spec_cell (q.shift i) contents[i] value) <;> iframe

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
  have hReadable := readable_of_pointsTo hPointsToFrame
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hPointsTo
  have hSlot := Heap.isValid_cell q.cellPtr (Pointee.toCell value)
  have hValid : Heap.IsValid (Heap.cell q.cellPtr (Pointee.toCell value) ∪ rest) q.cellPtr :=
    Heap.isValid_union_left hSlot
  refine ⟨hReadable, (Heap.borrow q.cellPtr _ hValid).2,
    Heap.compatible_borrow_left hCompatible hValid, ?_, ?_⟩
  · exact congrArg Prod.snd (Heap.borrow_union_left (h₂ := frame) q.cellPtr hValid)
  · have hBorrowedRest : PartialCommMonoid.Compatible (Heap.borrowedSlot q.loc) rest := by
      have hBorrowed := Heap.compatible_borrow_left hCompatibleRest hSlot
      rwa [Heap.borrow_cell] at hBorrowed
    refine (sep_pure_l _ _ _).mpr ⟨get_of_pointsTo hPointsToFrame hReadable, ?_⟩
    rw [show hValid = Heap.isValid_union_left hSlot from Subsingleton.elim _ _,
      Heap.borrow_union_left q.cellPtr hSlot]
    simp only [Prod.map_snd, Heap.borrow_cell]
    exact Heap.Subheap.union_left hBorrowedRest

@[step]
theorem endBorrow.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦† 1 ⦄ q.endBorrow value ⦃ q ↦ value⦄ := by
  rw [pointsToBorrowed_one]
  apply ispec_guardedModify
  intro h hBorrowedSub frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hBorrowedSub
  have hSlot : Heap.IsBorrowed (Heap.borrowedSlot q.cellPtr.loc) q.cellPtr.loc :=
    Heap.isBorrowed_borrowedSlot q.loc
  have hBorrowed : Heap.IsBorrowed (Heap.borrowedSlot q.cellPtr.loc ∪ rest) q.cellPtr.loc :=
    Heap.isBorrowed_union_left hSlot
  refine ⟨Heap.isBorrowed_union_left hBorrowed,
    (Heap.endBorrow q.cellPtr (Pointee.toCell value) _ hBorrowed).2,
    Heap.compatible_endBorrow_left hCompatible hBorrowed, ?_, ?_⟩
  · exact congrArg Prod.snd
      (Heap.endBorrow_union_left (h₂ := frame) q.cellPtr (Pointee.toCell value) hBorrowed)
  · have hLiveRest :
        PartialCommMonoid.Compatible (Heap.cell q.cellPtr (Pointee.toCell value)) rest := by
      have hLive := Heap.compatible_endBorrow_left (value := Pointee.toCell value) (q := q.cellPtr)
        hCompatibleRest hSlot
      rwa [Heap.endBorrow_borrowedSlot] at hLive
    show Heap.Subheap _ _
    rw [show hBorrowed = Heap.isBorrowed_union_left hSlot from Subsingleton.elim _ _,
      Heap.endBorrow_union_left q.cellPtr _ hSlot]
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

@[step]
theorem RawPtr.as_mut_unchecked.spec (q : MutRawPtr T) (value : T) :
    ⦃ q ↦ value ⦄ q.as_mut_unchecked
      ⦃ (result, back) => ⌜result = value ∧ back = q.endBorrow⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.as_mut_unchecked
  apply WP.ispec_bind (RawPtr.borrow.spec q value)
  · iframe
  · intro v
    apply (ispec_ok _).2
    simp only [uncurry_apply_pair]
    iframe

@[step]
theorem RawPtr.as_ref_unchecked.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.as_ref_unchecked
      ⦃ (result, back) => ⌜result = value ∧ back = q.endBorrow value⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.as_ref_unchecked
  apply WP.ispec_bind (RawPtr.borrow.spec q value)
  · iframe
  · intro v
    apply (ispec_ok _).2
    simp only [uncurry_apply_pair]
    iframe

omit [Pointee T] in
theorem RawPtr.eq.spec_self [NonZeroSized T] (q : RawPtr T M) :
    ⦃ emp ⦄ q.eq q ⦃ b => ⌜b = true⌝⦄ := by
  rw [RawPtr.eq, ite_eq_left rfl]
  apply (ispec_ok _).2
  iframe

omit [Pointee T] in
/-- Two different pointers into the same allocation are different. -/
theorem RawPtr.eq.spec_same_alloc [NonZeroSized T] (hNZ : NonZeroSized.nonZero T)
    {p q : RawPtr T M} (hNe : p ≠ q) (hBase : p.loc.allocId = q.loc.allocId) :
    ⦃ emp ⦄ p.eq q ⦃ b => ⌜b = false⌝⦄ := by
  rw [RawPtr.eq, ite_eq_right fun h => hNe (RawPtr.ext h)]
  apply ispec_guardedModify
  intro h hEmp frame hCompatible
  exact ⟨⟨hNZ, .inl hBase⟩, h, hCompatible, rfl, (pure_holds h).mpr rfl⟩

/-- Two pointers to different live boxes are different. -/
theorem RawPtr.eq.spec_boxes [NonZeroSized T] (hNZ : NonZeroSized.nonZero T)
    {p q : RawPtr T M} (hNe : p ≠ q) (v w : T) :
    ⦃ p ↦ v ∗ p.freeable ∗ q ↦ w ∗ q.freeable ⦄ p.eq q
      ⦃ b => ⌜b = false⌝ ∗ (p ↦ v ∗ p.freeable ∗ q ↦ w ∗ q.freeable)⦄ := by
  rw [RawPtr.eq, ite_eq_right fun h => hNe (RawPtr.ext h)]
  apply ispec_guardedModify
  intro h hPre frame hCompatible
  have hSub : Heap.Subheap h (h ∪ frame) := Heap.Subheap.union_left hCompatible
  have liveBox : ∀ r : RawPtr T M, ∀ u : T,
      (iprop(p ↦ v ∗ p.freeable ∗ q ↦ w ∗ q.freeable) ⊢ iprop(r ↦ u ∗ r.freeable)) →
      r.LiveBox (h ∪ frame) := fun r u hEntails => by
    have hR := hEntails h hPre
    refine ⟨Heap.isLive_of_isValid (q := r.cellPtr) (RawPtr.isValid_of_pointsToCell
      ((r ↦ u).up_closed (SepLogic.sep_elim_right _ _ h hR) hSub)), ?_⟩
    exact Heap.Subheap.isEndMarker
      (((RawPtr.freeable_holds r h).mp (SepLogic.sep_elim_left _ _ h hR)).2.trans hSub)
  exact ⟨⟨hNZ, .inr ⟨liveBox p v (by iframe), liveBox q w (by iframe)⟩⟩, h, hCompatible, rfl,
    pure_sep_intro _ rfl h hPre⟩

omit [Pointee T] in
/-- Comparing a pointer to a borrow view (see `core.ptr.from_mut.spec`) with a pointer into
another allocation fails. -/
theorem RawPtr.eq.fails_view [NonZeroSized T] {p q : RawPtr T M}
    (hBase : p.loc.allocId ≠ q.loc.allocId) :
    ifails (p.freeable 1 .view) (p.eq q) := by
  rw [RawPtr.eq, ite_eq_right fun h => hBase (congrArg Loc.allocId h)]
  apply ifails_guardedModify
  intro h hFreeable h' hSub hPre
  rcases hPre.2 with hEq | ⟨⟨_, hBox⟩, _⟩
  · exact hBase hEq
  · nomatch Heap.isEndMarker_unique (Heap.Subheap.isEndMarker (hFreeable.2.trans hSub)) hBox

/-- Comparing two pointers to different slots of a type which may be zero-sized fails. -/
theorem RawPtr.eq.fails_zero_sized [NonZeroSized T] (hZ : NonZeroSized.nonZero T = false)
    {p q : RawPtr T M} (v w : T) : ifails (p ↦ v ∗ q ↦ w) (p.eq q) := by
  by_cases hA : p.loc = q.loc
  · refine ifails_mono (P' := ⌜False⌝ ∗ emp) ?_ (ifails_ipure False.elim)
    rw [sep_emp_r_eq, RawPtr.ext hA]
    exact RawPtr.pointsTo_exclusive q v w
  · rw [RawPtr.eq, ite_eq_right hA]
    apply ifails_guardedModify
    intro _ _ _ _ hPre
    exact absurd hPre.1 (by simp [hZ])

/-! ### Undefined behaviours rejected by the model -/

namespace RawPtr

/-- Reading a cell which holds no value of the pointee (for instance, uninitialized memory) fails. -/
theorem read.fails_cell (q : RawPtr T M) (content : Option (Pointee.Cell T))
    (hNone : Pointee.ofCell content = none) :
    ifails (q ↦? content) q.read := by
  apply ifails_guardedModify
  intro h hPointsTo h' hSub hReadable
  have hInit := hReadable.init
  rw [Heap.read_of_subheap (hPointsTo.trans hSub), hNone] at hInit
  exact Bool.false_ne_true hInit

/-- Reading uninitialized memory fails. -/
theorem read.fails_uninit (q : RawPtr T M)
    (hNone : Pointee.ofCell (none : Option (Pointee.Cell T)) = none) :
    ifails (q ↦? none) q.read :=
  read.fails_cell q none hNone

/-- Reading a borrowed slot (moved out by `from_raw_parts`) fails. -/
theorem read.fails_borrowed (q : RawPtr T M) : ifails (q ↦† 1) q.read := by
  rw [pointsToBorrowed_one]
  apply ifails_guardedModify
  intro h hBorrowed h' hSub hReadable
  exact Heap.not_isLive_of_isBorrowed (Heap.Subheap.isBorrowed (hBorrowed.trans hSub))
    (Heap.isLive_of_isValid (q := q.cellPtr) hReadable.valid)

/-- Reading freed memory fails. -/
theorem read.fails_freed (q : RawPtr T M) : ifails q.freed q.read := by
  apply ifails_guardedModify
  intro h hFreed h' hSub hReadable
  exact Heap.not_isLive_of_isFreed (Heap.Subheap.isFreed
    ((show Heap.Subheap (Heap.freedSlot q.loc) h from hFreed).trans hSub))
    (Heap.isLive_of_isValid (q := q.cellPtr) hReadable.valid)

/-- Reading the end marker of an allocation (one past its last cell) fails. -/
theorem read.fails_end (q : RawPtr T M) (count : Nat) (kind : AllocKind) :
    ifails (q.freeable count kind) (q.shift count).read := by
  apply ifails_guardedModify
  intro h hFreeable h' hSub hReadable
  exact Heap.not_isLive_of_isEndMarker (Heap.Subheap.isEndMarker (hFreeable.2.trans hSub))
    (by simpa [cellPtr] using Heap.isLive_of_isValid (q := (q.shift count).cellPtr) hReadable.valid)

/-- Borrowing a value which is already borrowed fails. -/
theorem borrow.fails_borrowed (q : RawPtr T M) : ifails (q ↦† 1) q.borrow := by
  rw [pointsToBorrowed_one]
  apply ifails_guardedModify
  intro h hBorrowed h' hSub hReadable
  exact Heap.not_isLive_of_isBorrowed (Heap.Subheap.isBorrowed (hBorrowed.trans hSub))
    (Heap.isLive_of_isValid (q := q.cellPtr) hReadable.valid)

/-- `&mut *q` while `*q` is borrowed fails. -/
theorem as_mut_unchecked.fails_borrowed (q : MutRawPtr T) :
    ifails (q ↦† 1) q.as_mut_unchecked :=
  ifails_bind_left (borrow.fails_borrowed q)

/-- `&*q` while `*q` is borrowed fails. -/
theorem as_ref_unchecked.fails_borrowed (q : RawPtr T M) :
    ifails (q ↦† 1) q.as_ref_unchecked :=
  ifails_bind_left (borrow.fails_borrowed q)

/-- Moving out of a cell which holds no value of the pointee fails. -/
theorem borrow.fails_cell (q : RawPtr T M) (content : Option (Pointee.Cell T))
    (hNone : Pointee.ofCell content = none) :
    ifails (q ↦? content) q.borrow := by
  apply ifails_guardedModify
  intro h hPointsTo h' hSub hReadable
  have hInit := hReadable.init
  rw [Heap.read_of_subheap (hPointsTo.trans hSub), hNone] at hInit
  exact Bool.false_ne_true hInit

/-- Borrowing a range which contains a cell holding no value of the pointee (for instance, an
uninitialized cell) fails. -/
theorem borrowRange.fails (q : RawPtr T M) (values : List T)
    (content : Option (Pointee.Cell T)) (hNone : Pointee.ofCell content = none) (n : Nat)
    (hn : values.length < n) :
    ifails iprop(q ↦* values ∗ (q.shift values.length) ↦? content) (q.borrowRange n) := by
  induction values generalizing q n with
  | nil =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [borrowRange]
    apply ifails_bind_left
    refine ifails_mono ?_ (borrow.fails_cell q content hNone)
    simp only [pointsToRange_nil, List.length_nil, shift_zero]
    iframe
  | cons value values ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [borrowRange]
    have hF := ispec_frame (borrow.spec q value)
      iprop((q.shift 1) ↦* values ∗ ((q.shift 1).shift values.length) ↦? content)
    refine ifails_mono ?_ (ifails_bind hF fun x => ifails_bind_left
      (ifails_mono ?_ (ih (q.shift 1) m (by simp at hn; omega))))
    · rw [pointsToRange_cons, List.length_cons, shift_shift, Nat.add_comm]
      iframe
    · exact SepLogic.sep_elim_left _ _

end RawPtr

end

end Aeneas.Std
