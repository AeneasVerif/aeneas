/- `core::ptr` -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Delab
public import Aeneas.Std.Heap
public import Aeneas.SepLogic.IProp
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.SliceDef
public import Aeneas.Std.Array.Array
public import Aeneas.Data.BitVec
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

/-! ### START Trusted definitions

`core::ptr`: the raw-pointer methods (from `core::ptr::mut_ptr` and `core::ptr::const_ptr`) and the
module functions. Each definition with a `rust_fun` pattern models that Rust function, with the
signature Aeneas gives it: `Box<T>` is `T`, and a `&mut T` argument is returned updated next to the
result. The others are not Rust functions: the cell operations (`HeapOp`), `RawPtr.load`, the
heap-model operations which build the models of the conversions between borrows and raw pointers
(`RawPtr.alloc`, `allocView`, `endView`, `borrow`, `endBorrow` and their range versions),
`Pointee.decode`, `RawPtr.null`, `RawPtr.LiveBox`, and `RawPtr.eq` and `RawPtr.ne`, which model `==`
and `!=` on raw pointers.

The heap is a map from locations (an allocation and an offset) to cells. A pointer `*mut T` reads
and writes the `Pointee.size T` cells of type `Pointee.Cell T` from its location on, and decodes
them with `Pointee.ofCells` (see `Pointee`). There are two kinds of cells:
- byte cells (`U8`), for the types which have a fixed, total byte representation (integers,
  `bool`, arrays of them, `MaybeUninit` of them): the cells of a value are its bytes, so that
  reading memory at another such type (after a pointer cast, `read_unaligned`, a transmute...)
  decodes the same bytes differently, as in Rust (little-endian, 64-bit layouts);
- typed cells (`TypedCell T`), one per value, for the other types (in particular pointers, whose
  bytes we do not model): accessing them at another type `U` fails if `TypedCell T ≠ TypedCell U`
  (when the two types have the same cardinality, this inequality can not be proved, and neither
  can the success of the access).

Every access checks the type of the cells (so that casting a pointer is safe: `<*mut T>::cast` and
`as` casts only change the type of the pointer), that the pointer is not null, and, if it requires
it, the alignment of the pointer (`RawPtr.Aligned`). Pointer arithmetic is only allowed over the
cells of the pointee (`RawPtr.InBounds`). The extraction only accepts the casts and transmutes
between types which do not mention `Box`, references, or `repr(packed)`/`repr(align)` types
(several Rust types share the same Lean type: `Box<T>` and `&T` are `T`, and a tuple structure with
one field is its field). -/

/-- The cell holding a value of a type without byte representation. -/
structure TypedCell (T : Type) where
  val : T

/-- How the values of `T` are stored in the heap: a value is `size` cells of type `Cell`, each of
which may be uninitialized (`none`). `ofCells` decodes the cells found in the heap, if they hold a
value of `T`: for instance, reading uninitialized memory fails unless `T` can represent it
(`MaybeUninit`).

An instance is an assumption about the memory representation of the Rust type modelled by `T`:
the byte instances (`Cell = U8`) must give the bytes of the values and the Rust `size` and
`align`ment (a power of two), and the Rust type must not be zero-sized if `nonZero` is `true`.
Typed instances (`Pointee.typed`, `Cell = TypedCell T`, one cell per value, alignment `1`) are
always safe: their cells can only be accessed at the type `T` (or at arrays and `MaybeUninit` of
`T`, whose cells are those of `T`). The laws needed by the proofs are in `Pointee.Lawful`.

Generic code takes the instances of its type parameters as arguments (`[Pointee T]` binders,
added by the extraction to the stateful functions). The definitions which are elaborated without
the instance of a type parameter (e.g., the implementations of a trait for a generic type) use
`Pointee.default`, whose cells are typed: they can not access the cells of byte types. -/
class Pointee (T : Type) where
  Cell : Type
  size : Nat
  align : Nat
  nonZero : Bool
  toCells : T → List (Option Cell)
  ofCells : List (Option Cell) → Option T

/-- One typed cell per value: the cells can not be read at another type. `nonZero` tells whether
the Rust type is known not to be zero-sized (see `RawPtr.eq`). -/
@[instance_reducible] def Pointee.typed (T : Type) (nonZero : Bool) : Pointee T where
  Cell := TypedCell T
  size := 1
  align := 1
  nonZero := nonZero
  toCells value := [some ⟨value⟩]
  ofCells
    | [some cell] => some cell.val
    | _ => none

/-- By default, a value is stored in a typed cell, and the type may be zero-sized. -/
instance (priority := low) Pointee.default {T : Type} : Pointee T := Pointee.typed T false

/-- The byte cells of a type: `encode` gives the bytes of a value, and `decode` the value whose
bytes are given (if any). -/
@[instance_reducible] def Pointee.bytes (T : Type) (size align : Nat) (encode : T → List U8)
    (decode : List U8 → Option T) : Pointee T where
  Cell := U8
  size := size
  align := align
  nonZero := size != 0
  toCells value := (encode value).map some
  ofCells cells := cells.mapM id >>= decode

/-- Little-endian bytes of `numBits` bits. -/
def Pointee.decodeLE (numBits : Nat) (bytes : List U8) : Option (BitVec numBits) :=
  if h : 8 * bytes.length = numBits then
    some ((BitVec.fromLEBytes (bytes.map U8.bv)).cast (by simpa using h))
  else none

instance UScalar.instPointee (ty : UScalarTy) : Pointee (UScalar ty) :=
  Pointee.bytes (UScalar ty) (ty.numBits / 8) (ty.numBits / 8)
    (fun x => x.bv.toLEBytes.map UScalar.mk)
    (fun bytes => (Pointee.decodeLE ty.numBits bytes).map UScalar.mk)

instance IScalar.instPointee (ty : IScalarTy) : Pointee (IScalar ty) :=
  Pointee.bytes (IScalar ty) (ty.numBits / 8) (ty.numBits / 8)
    (fun x => x.bv.toLEBytes.map UScalar.mk)
    (fun bytes => (Pointee.decodeLE ty.numBits bytes).map IScalar.mk)

/-- A `bool` is a byte, `0` or `1`: reading another byte as a `bool` fails. -/
instance Bool.instPointee : Pointee Bool :=
  Pointee.bytes Bool 1 1 (fun b => [if b then 1#u8 else 0#u8])
    (fun
      | [byte] => if byte.val = 0 then some false else if byte.val = 1 then some true else none
      | _ => none)

/-- The values decoded from consecutive runs of `size T` cells. -/
def Pointee.ofCellsList (T : Type) [Pointee T] :
    Nat → List (Option (Pointee.Cell T)) → Option (List T)
  | 0, _ => some []
  | n + 1, cells => do
    let value ← Pointee.ofCells (cells.take (Pointee.size T))
    let values ← Pointee.ofCellsList T n (cells.drop (Pointee.size T))
    some (value :: values)

/-- The cells of an array are the cells of its elements. -/
instance Array.instPointee {T : Type} [Pointee T] {n : Usize} : Pointee (Array T n) where
  Cell := Pointee.Cell T
  size := n.val * Pointee.size T
  align := Pointee.align T
  nonZero := n.val != 0 && Pointee.nonZero T
  toCells a := a.val.flatMap Pointee.toCells
  ofCells cells := do
    let values ← Pointee.ofCellsList T n.val cells
    if h : values.length = n.val then some (Array.from values h) else none

instance Option.instPointee {T : Type} [Pointee T] : Pointee (Option T) :=
  Pointee.typed (Option T) (Pointee.nonZero T)

instance RawPtr.instPointee {T : Type _} {M : Mutability} : Pointee (RawPtr T M) :=
  Pointee.typed (RawPtr T M) true

instance Char.instPointee : Pointee Char := Pointee.typed Char true

/-- The cells of a value, or `size` uninitialized cells. -/
def Pointee.optCells {T : Type} [Pointee T] : Option T → List (Option (Pointee.Cell T))
  | some value => Pointee.toCells value
  | none => List.replicate (Pointee.size T) none

/-- Not a Rust function: decodes cells, failing if they do not hold a value. -/
def Pointee.decode {T : Type} [Pointee T] (cells : List (Option (Pointee.Cell T))) : Result T :=
  match Pointee.ofCells cells with
  | some value => .ok value
  | none => .fail .undef

/-! The operations on the cells of type `α` from `l` on, which the pointer operations are made of.
`l` is the location of a pointer to `α` (`⟨l⟩ : MutRawPtr α`). -/
namespace HeapOp

/-- The content of the live cell of type `α` at `l`. -/
def read (α : Type) (l : Loc) : Result (Option α) :=
  Result.guardedModify (fun h => Heap.IsValid h (⟨l⟩ : MutRawPtr α)) fun h hValid =>
    ((h.read (⟨l⟩ : MutRawPtr α) hValid).1, h)

def reads (α : Type) (l : Loc) : Nat → Result (List (Option α))
  | 0 => .ok []
  | n + 1 => do
    let content ← read α l
    let contents ← reads α (l.shift 1) n
    .ok (content :: contents)

/-- Overwrites the live cell of type `α` at `l`. -/
def write {α : Type} (l : Loc) (content : Option α) : Result Unit :=
  Result.guardedModify _ (Heap.write (⟨l⟩ : MutRawPtr α) content)

def writes {α : Type} (l : Loc) : List (Option α) → Result Unit
  | [] => .ok ()
  | content :: contents => do
    write l content
    writes (l.shift 1) contents

/-- Moves the content of the live cell of type `α` at `l` out, and marks the slot as borrowed. -/
def borrow (α : Type) (l : Loc) : Result (Option α) :=
  Result.guardedModify _ (Heap.borrow (⟨l⟩ : MutRawPtr α))

def borrows (α : Type) (l : Loc) : Nat → Result (List (Option α))
  | 0 => .ok []
  | n + 1 => do
    let content ← borrow α l
    let contents ← borrows α (l.shift 1) n
    .ok (content :: contents)

/-- Ends the borrow of the slot at `l`, which holds `content` again. -/
def endBorrow {α : Type} (l : Loc) (content : Option α) : Result Unit :=
  Result.guardedModify _ (Heap.endBorrow (⟨l⟩ : MutRawPtr α) content)

def endBorrows {α : Type} (l : Loc) : List (Option α) → Result Unit
  | [] => .ok ()
  | content :: contents => do
    endBorrow l content
    endBorrows (l.shift 1) contents

/-- The `n` cells from `l` on are live cells of type `α`. -/
def Live (α : Type) (h : Heap) (l : Loc) (n : Nat) : Prop :=
  ∀ i < n, Heap.IsValid h (⟨l.shift i⟩ : MutRawPtr α)

end HeapOp

namespace RawPtr

/-- `q` as a pointer to the cells of its pointee. -/
@[reducible] def cellPtr {T : Type} [Pointee T] (q : RawPtr T M) : RawPtr (Pointee.Cell T) M :=
  ⟨q.loc⟩

/-- `q` moved `i` values forward, for specifications. Programs use `add`. -/
def shift {T : Type} [Pointee T] (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  q.shiftCells (i * Pointee.size T)

/-- `q` is not null, for an access to `n` cells. Rust requires it for every access, even one which
touches no byte (zero-sized values, zero values). An access to cells checks that they are live,
and the allocation `0` is never allocated (`Heap.freshAllocId`): we only need to check it when no
cell is accessed. This is conservative: `NonNull::dangling()` (allocation `0`) can not be used to
access zero-sized values. -/
def NotNull (q : RawPtr T M) (n : Nat) : Prop := n = 0 → q.loc.allocId ≠ 0

/-- `q` is aligned for `T` (and not null, see `NotNull`). The identifier of an allocation is an
odd multiple of the alignment Rust guarantees for it (`Heap.freshAllocId`), and its cells are bytes
or typed cells (whose alignment is `1`, see `Pointee`): the address of `q` is a multiple of
`align T` if both the identifier and the offset are. This is conservative: an allocation may be more
aligned than its type requires. -/
def Aligned {T : Type} [Pointee T] (q : RawPtr T M) : Prop :=
  Pointee.align T ∣ q.loc.allocId ∧ Pointee.align T ∣ q.loc.offset ∧ q.NotNull (Pointee.size T)

/-- The cells of the `n` values from `q` on are live cells of the type of the cells of `T` (`add`
stays in bounds). Pointer arithmetic counts cells, which are bytes for the byte types, and values
for the typed ones: it is only allowed over the cells of the pointee, so that `size T` cells are
`size_of::<T>()` bytes or one value. -/
def InBounds {T : Type} [Pointee T] (q : RawPtr T M) (n : Nat) (h : Heap) : Prop :=
  HeapOp.Live (Pointee.Cell T) h q.loc (n * Pointee.size T)

end RawPtr

/-! #### Heap-model operations
Aeneas builds its models of Rust's raw-pointer functions (`from_mut`, `from_ref`, `as_ptr`,
`as_mut_ptr`, `from_raw_parts`, `from_raw_parts_mut`, `Box::into_raw`...) from the operations below,
which act on the model's heap directly. -/

/-- A fresh allocation of kind `kind` holding `values`, aligned for `T`. Fresh memory is mutable in
Rust. -/
def RawPtr.alloc {T : Type} [Pointee T] (values : List T) (kind : AllocKind) :
    Result (MutRawPtr T) :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (⟨Heap.freshLoc h (Pointee.align T)⟩,
      (h.alloc (Pointee.align T) (values.flatMap Pointee.toCells) kind).2)

/-- Allocates a raw-pointer view of a place that the functional translation represents as a plain
value, without an address. Used by `from_mut`, `from_ref`, `as_ptr` and `as_mut_ptr`. The view is a
fresh allocation holding a copy of `values`, which only `endView` frees (`AllocKind.view`). -/
def RawPtr.allocView {T : Type} [Pointee T] (values : List T) : Result (MutRawPtr T) :=
  RawPtr.alloc values .view

/-- Frees the view of `count` values at `q`. -/
def RawPtr.endView {T : Type} [Pointee T] (q : RawPtr T M) (count : Nat) : Result Unit :=
  Result.guardedModify _ (Heap.dealloc q (count * Pointee.size T) .view)

/-- Decodes the value `q` points to, without the checks of `read`. -/
def RawPtr.load {T : Type} [Pointee T] (q : RawPtr T M) : Result T := do
  let cells ← HeapOp.reads (Pointee.Cell T) q.loc (Pointee.size T)
  Pointee.decode cells

/-- Moves the value out of the cells of `q`, whose slots are borrowed, so that every access to them
through a raw pointer fails until the borrow is ended with `endBorrow`. -/
def RawPtr.borrow {T : Type} [Pointee T] (q : RawPtr T M) : Result T := do
  let cells ← HeapOp.borrows (Pointee.Cell T) q.loc (Pointee.size T)
  Pointee.decode cells

/-- Ends the borrow of the cells of `q`, which hold `value` again. -/
def RawPtr.endBorrow {T : Type} [Pointee T] (q : RawPtr T M) (value : T) : Result Unit :=
  HeapOp.endBorrows q.loc (Pointee.toCells value)

/-- `borrow` on the `n` values from `q` on. -/
def RawPtr.borrowRange {T : Type} [Pointee T] (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.borrow
    let values ← (q.shift 1).borrowRange n
    .ok (value :: values)

/-- `endBorrow` on the `values.length` values from `q` on. -/
def RawPtr.endBorrowRange {T : Type} [Pointee T] (q : RawPtr T M) : List T → Result Unit
  | [] => .ok ()
  | value :: values => do
    q.endBorrow value
    (q.shift 1).endBorrowRange values

/-- `load` on the `n` values from `q` on. -/
def RawPtr.readRange {T : Type} [Pointee T] (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.load
    let values ← (q.shift 1).readRange n
    .ok (value :: values)

/-! #### Pointer arithmetic and casts -/

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::add"]
def RawPtr.add {T : Type} [Pointee T] (q : RawPtr T M) (count : Usize) : Result (RawPtr T M) :=
  Result.guardedModify (fun h => q.InBounds count.val h) fun h _ => (q.shift count.val, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::add"] RawPtr.add

/-- `offset` by a signed number of values: the cells between the pointer and the result must be
live cells of the pointee (in particular, the result stays in the allocation). -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::offset"]
def RawPtr.offsetBy {T : Type} [Pointee T] (q : RawPtr T M) (count : Isize) :
    Result (RawPtr T M) :=
  let target : Int := q.loc.offset + count.val * Pointee.size T
  Result.guardedModify
    (fun h => 0 ≤ target ∧ HeapOp.Live (Pointee.Cell T) h
      ⟨q.loc.allocId, min q.loc.offset target.toNat⟩ (target - q.loc.offset).natAbs)
    fun h _ => (⟨⟨q.loc.allocId, target.toNat⟩⟩, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::offset"] RawPtr.offsetBy

/-- The distance between two pointers, in values: they must point into the same allocation, the
cells between them must be live cells of the pointee, the distance must be a multiple of the size
of `T`, which must not be zero-sized. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::offset_from"]
def RawPtr.offset_from {T : Type} [Pointee T] (p : RawPtr T M) (origin : RawPtr T M') :
    Result Isize :=
  let distance : Int := ((p.loc.offset : Int) - origin.loc.offset) / Pointee.size T
  Result.guardedModify
    (fun h => p.loc.allocId = origin.loc.allocId ∧ Pointee.nonZero T ∧ Pointee.size T ≠ 0 ∧
      (Pointee.size T : Int) ∣ ((p.loc.offset : Int) - origin.loc.offset) ∧
      HeapOp.Live (Pointee.Cell T) h ⟨p.loc.allocId, min p.loc.offset origin.loc.offset⟩
        ((p.loc.offset : Int) - origin.loc.offset).natAbs ∧
      -2 ^ (IScalarTy.Isize.numBits - 1) ≤ distance ∧ distance < 2 ^ (IScalarTy.Isize.numBits - 1))
    fun h hPre => (IScalar.ofIntCore distance ⟨hPre.2.2.2.2.2.1, hPre.2.2.2.2.2.2⟩, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::offset_from"] RawPtr.offset_from

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast_const" -canFail -lift]
def RawPtr.cast_const (q : MutRawPtr T) : ConstRawPtr T :=
  ⟨q.loc⟩

/-- Changes the pointee type: the accesses through the new pointer check that the cells have the
type of the cells of the new pointee, and decode them (see `Pointee`). -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast" -canFail -lift]
def RawPtr.cast {T : Type _} {M : Mutability} (U : Type _) (q : RawPtr T M) : RawPtr U M :=
  ⟨q.loc⟩

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::cast" -canFail -lift] RawPtr.cast

/-! #### Accesses -/

namespace RawPtr

/-- Reads the value `q` points to, which need not be aligned. -/
@[rust_fun "core::ptr::const_ptr::{*const @T}::read_unaligned"]
def read_unaligned {T : Type} [Pointee T] (q : RawPtr T M) : Result T := do
  Result.require (q.NotNull (Pointee.size T))
  q.load

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read_unaligned"] read_unaligned
attribute [rust_fun "core::ptr::read_unaligned"] read_unaligned

@[rust_fun "core::ptr::const_ptr::{*const @T}::read"]
def read {T : Type} [Pointee T] (q : RawPtr T M) : Result T := do
  Result.require q.Aligned
  q.read_unaligned

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read"] read
attribute [rust_fun "core::ptr::read"] read
attribute [rust_fun "core::ptr::const_ptr::{*const @T}::read_volatile"] read
attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read_volatile"] read
attribute [rust_fun "core::ptr::read_volatile"] read

end RawPtr

/-- Writes a value, which need not be aligned. Writing initializes the cells, which may be
uninitialized. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write_unaligned"]
def MutRawPtr.write_unaligned {T : Type} [Pointee T] (q : MutRawPtr T) (value : T) :
    Result Unit := do
  Result.require (q.NotNull (Pointee.size T))
  HeapOp.writes q.loc (Pointee.toCells value)

attribute [rust_fun "core::ptr::write_unaligned"] MutRawPtr.write_unaligned

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write"]
def MutRawPtr.write {T : Type} [Pointee T] (q : MutRawPtr T) (value : T) : Result Unit := do
  Result.require q.Aligned
  q.write_unaligned value

attribute [rust_fun "core::ptr::write"] MutRawPtr.write
attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::write_volatile"] MutRawPtr.write
attribute [rust_fun "core::ptr::write_volatile"] MutRawPtr.write

/-- Copies the cells of `count` values, initialized or not (`memmove`). -/
@[rust_fun "core::ptr::copy"]
def core.ptr.copy {T : Type} [Pointee T] (src : ConstRawPtr T) (dst : MutRawPtr T)
    (count : Usize) : Result Unit := do
  Result.require (src.Aligned ∧ dst.Aligned ∧ src.NotNull (count.val * Pointee.size T) ∧
    dst.NotNull (count.val * Pointee.size T))
  let cells ← HeapOp.reads (Pointee.Cell T) src.loc (count.val * Pointee.size T)
  HeapOp.writes dst.loc cells

/-- `copy`, on ranges which must not overlap. -/
@[rust_fun "core::ptr::copy_nonoverlapping"]
def core.ptr.copy_nonoverlapping {T : Type} [Pointee T] (src : ConstRawPtr T)
    (dst : MutRawPtr T) (count : Usize) : Result Unit := do
  let n := count.val * Pointee.size T
  Result.require (src.loc.allocId ≠ dst.loc.allocId ∨ src.loc.offset + n ≤ dst.loc.offset ∨
    dst.loc.offset + n ≤ src.loc.offset)
  core.ptr.copy src dst count

/-- Sets the bytes of `count` values to `value`: the cells must be bytes. -/
@[rust_fun "core::ptr::write_bytes"]
def core.ptr.write_bytes {T : Type} [Pointee T] (dst : MutRawPtr T) (value : U8)
    (count : Usize) : Result Unit := do
  Result.require (Pointee.Cell T = U8 ∧ dst.Aligned ∧ dst.NotNull (count.val * Pointee.size T))
  HeapOp.writes dst.loc (List.replicate (count.val * Pointee.size T) (some value))

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::write_bytes"] core.ptr.write_bytes

/-- Reinterprets the cells of a value at another type: the cells must have the same type and
number, and hold a value of the target type. -/
@[rust_fun "core::intrinsics::transmute"]
def core.mem.transmute {A : Type} (B : Type) [Pointee A] [Pointee B] (x : A) : Result B :=
  Aeneas.Std.bind
    (Result.guardedModify (fun _ => Pointee.Cell A = Pointee.Cell B ∧ Pointee.size A = Pointee.size B)
      fun h hEq => (cast (congrArg (fun α => List (Option α)) hEq.1) (Pointee.toCells x), h))
    Pointee.decode

/-- Runs the destructor of the value (a no-op in the model: drops are not modelled): the value
must be valid, and its cells are left uninitialized. -/
@[rust_fun "core::ptr::drop_in_place"]
def core.ptr.drop_in_place {T : Type} [Pointee T] (p : MutRawPtr T) : Result Unit :=
  Aeneas.Std.bind p.read fun _ => HeapOp.writes p.loc (Pointee.optCells (none : Option T))

/-! #### Borrows -/

/-- Back function of `from_mut`: reads the value, with the writes made through the pointer, and
ends the view, so that the pointer can't be used anymore. -/
def core.ptr.end_from_mut {T : Type} [Pointee T] (p : MutRawPtr T) : Result T := do
  let value ← p.load
  p.endView 1
  .ok value

/-- The pointer is a view of `r`; the back computation runs when the borrow ends
(`statefulLifetimes`). -/
@[rust_fun "core::ptr::from_mut" (statefulLifetimes := [0])]
def core.ptr.from_mut {T : Type} [Pointee T] (r : T) : Result (MutRawPtr T × Result T) :=
  Aeneas.Std.bind (RawPtr.allocView [r]) fun p => .ok (p, core.ptr.end_from_mut p)

/-- Back function of `from_ref`: the cells must still hold the value (writing through a const
pointer cast to mut is UB), and the view is freed. -/
def core.ptr.end_from_ref {T : Type} [Pointee T] (r : T) (p : ConstRawPtr T) : Result Unit := do
  let value ← p.load
  p.endView 1
  Result.require (value = r)

/-- The pointer is a view of `r` (`&raw const place`, `ptr::addr_of!`). -/
@[rust_fun "core::ptr::from_ref" (statefulLifetimes := [0])]
def core.ptr.from_ref {T : Type} [Pointee T] (r : T) : Result (ConstRawPtr T × Result Unit) :=
  Aeneas.Std.bind (RawPtr.allocView [r]) fun p =>
    .ok (p.cast_const, core.ptr.end_from_ref r p.cast_const)

/-- `&mut *p`: the value is moved out of its cells, which are borrowed so that the other accesses to
them fail while the borrow is live, and get back the final value of the borrow when the borrow ends
(`statefulLifetimes`). The pointer must be aligned. The extraction translates the borrows of places
behind raw pointers (`&mut (*p).f`) to this function. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::as_mut_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) :
    Result (T × (T → Result Unit)) :=
  Aeneas.Std.bind (Result.require p.Aligned) fun _ =>
  Aeneas.Std.bind p.borrow fun value => .ok (value, p.endBorrow)

/-- `&*p`: like `as_mut_unchecked`, the value is moved out while the borrow is live, so that
writing through another pointer fails (this is conservative: reading through another pointer
also fails), and given back unchanged when the borrow ends. -/
@[rust_fun "core::ptr::const_ptr::{*const @T}::as_ref_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_ref_unchecked {T : Type} [Pointee T] (p : RawPtr T M) :
    Result (T × Result Unit) :=
  Aeneas.Std.bind (Result.require p.Aligned) fun _ =>
  Aeneas.Std.bind p.borrow fun value => .ok (value, p.endBorrow value)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::as_ref_unchecked" (statefulLifetimes := [0])]
  RawPtr.as_ref_unchecked

/-! #### Null pointers and comparisons -/

/-- The null pointer. The allocation `0` is never allocated (see `Heap.freshAllocId`): the
pointers to it can not be dereferenced. -/
def RawPtr.null : RawPtr T M := ⟨⟨0, 0⟩⟩

@[rust_fun "core::ptr::null" -canFail -lift]
def core.ptr.null (T : Type _) : ConstRawPtr T := RawPtr.null

@[rust_fun "core::ptr::null_mut" -canFail -lift]
def core.ptr.null_mut (T : Type _) : MutRawPtr T := RawPtr.null

/-- `q` points to the live cells of an allocation of the global allocator holding one value (a
box, see `Box::into_raw`), of a type which is not zero-sized. -/
def RawPtr.LiveBox {T : Type} [Pointee T] (q : RawPtr T M) (h : Heap) : Prop :=
  Pointee.size T ≠ 0 ∧ Heap.IsValid h q.cellPtr ∧
    Heap.IsEndMarker h (q.loc.shift (Pointee.size T)) .global

/-- Pointer comparison (`==` on raw pointers, `NonNull`). The model does not know the addresses:
two pointers are equal if they are the same. Otherwise they are different if they point to
different cells of the same allocation, all the cells between them being live cells of the pointee
(so that the cells are bytes, or values of `T`, and not, e.g., values of a zero-sized type
reached through a cast), or to two live boxes (live allocations do not overlap), and the
pointee is not zero-sized (`Pointee.nonZero`). In the other cases the comparison fails: in
particular, the pointers obtained from borrows (`from_mut`, `as_ptr`, `NonNull::from`...) point to
fresh copies of the borrowed values, whose actual addresses are those of the borrowed values, and
freed allocations may share their addresses with new ones. -/
def RawPtr.eq {T : Type} [Pointee T] (p q : RawPtr T M) : Result Bool :=
  if p.loc = q.loc then .ok true
  else Result.guardedModify
    (fun h => Pointee.nonZero T ∧
      (p.loc.allocId = q.loc.allocId ∧ HeapOp.Live (Pointee.Cell T) h
          ⟨p.loc.allocId, min p.loc.offset q.loc.offset⟩
          ((p.loc.offset : Int) - q.loc.offset).natAbs ∨
        p.LiveBox h ∧ q.LiveBox h))
    fun h _ => (false, h)

/-- `!=` on pointers (see `RawPtr.eq`). -/
def RawPtr.ne {T : Type} [Pointee T] (p q : RawPtr T M) : Result Bool :=
  Aeneas.Std.bind (p.eq q) fun b => .ok (!b)

/-! ### END Trusted definitions -/


/-! ### Assertions -/

namespace HeapOp

/-- Owning `n` borrowed slots from `l` on. -/
def borrowedAt (l : Loc) : Nat → IProp
  | 0 => emp
  | n + 1 => owns (Heap.borrowedSlot l) ∗ borrowedAt (l.shift 1) n

end HeapOp

namespace RawPtr

variable {T : Type} [Pointee T] {M : Mutability}

/-- `q` owns the cells `cells` (of the type of the cells of `T`) from `q` on. -/
def pointsToCells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) : IProp :=
  owns (Heap.array q.loc cells)

def pointsTo (q : RawPtr T M) (value : T) : IProp :=
  q.pointsToCells (Pointee.toCells value)

/-- `q` owns the `values.length` values from `q` on. -/
def pointsToRange (q : RawPtr T M) (values : List T) : IProp :=
  q.pointsToCells (values.flatMap Pointee.toCells)

/-- `q` owns the cells of a value, or uninitialized cells (`none`). -/
def pointsToOpt (q : RawPtr T M) (content : Option T) : IProp :=
  q.pointsToCells (Pointee.optCells content)

/-- `pointsToOpt` on the `contents.length` values from `q` on. -/
def pointsToOpts (q : RawPtr T M) (contents : List (Option T)) : IProp :=
  q.pointsToCells (contents.flatMap Pointee.optCells)

/-- `q` owns the borrowed slots of the `n` values from `q` on (borrowed by `borrow`, to be given
back by `endBorrow`). -/
def pointsToBorrowed (q : RawPtr T M) (n : Nat) : IProp :=
  HeapOp.borrowedAt q.loc (n * Pointee.size T)

/-- The right to deallocate the `count` values at `q` as an allocation of kind `kind`: `q` is at
offset `0` and owns the end marker of its allocation. Only the allocation functions hand it out:
`Global.allocate` (`.global`) and `allocView` (`.view`). Defined directly rather than as
`⌜_⌝ ∗ owns _` so that the separation-logic tactics treat it as one atom. -/
def freeable (q : RawPtr T M) (count : Nat := 1) (kind : AllocKind := .global) : IProp where
  holds h := q.loc.offset = 0 ∧
    Heap.Subheap (Heap.endMarker (q.loc.shift (count * Pointee.size T)) kind) h
  up_closed := fun ⟨hOffset, hSub⟩ hExtend => ⟨hOffset, hSub.trans hExtend⟩

end RawPtr

/-- `q` owns the freed slot at `q`: the memory at `q` was deallocated. -/
def RawPtr.freed (q : RawPtr T M) : IProp :=
  owns (Heap.freedSlot q.loc)

instance instPointsToRawPtr {T : Type} [Pointee T] {M : Mutability} :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

instance instPointsToRangeRawPtr {T : Type} [Pointee T] {M : Mutability} :
    PointsToRange (RawPtr T M) T := ⟨RawPtr.pointsToRange⟩

end Aeneas.Std

namespace Aeneas

scoped notation:50 q:50 " ↦† " n:50 => Std.RawPtr.pointsToBorrowed q n
scoped notation:50 q:50 " ↦# " cells:50 => Std.RawPtr.pointsToCells q cells
scoped notation:50 q:50 " ↦? " content:50 => Std.RawPtr.pointsToOpt q content
scoped notation:50 q:50 " ↦*? " contents:50 => Std.RawPtr.pointsToOpts q contents

end Aeneas

namespace Aeneas.Std

open Aeneas

/-! ### Laws of the instances -/

/-- The laws of a `Pointee` instance used by the proofs (they are not needed by the model). -/
class Pointee.Lawful (T : Type) [Pointee T] : Prop where
  length_toCells (value : T) : (Pointee.toCells value).length = Pointee.size T
  ofCells_toCells (value : T) : Pointee.ofCells (Pointee.toCells value) = some value
  align_pos : 0 < Pointee.align T
  align_dvd_size : Pointee.align T ∣ Pointee.size T

/-- Uninitialized cells hold no value of `T` (see `MaybeUninit`). -/
class Pointee.UninitInvalid (T : Type) [Pointee T] : Prop where
  ofCells_uninit :
    Pointee.ofCells (List.replicate (Pointee.size T) none : List (Option (Pointee.Cell T))) = none

namespace Pointee

theorem typed.lawful (T : Type) (nonZero : Bool) : @Lawful T (typed T nonZero) :=
  @Lawful.mk T (typed T nonZero) (fun _ => rfl) (fun _ => rfl) Nat.one_pos (Nat.dvd_refl 1)

instance typed.instLawful {T : Type} {nonZero : Bool} : @Lawful T (typed T nonZero) :=
  typed.lawful T nonZero

instance default.instLawful {T : Type} : @Lawful T Pointee.default := typed.lawful T false

instance typed.instUninitInvalid {T : Type} {nonZero : Bool} :
    @UninitInvalid T (typed T nonZero) :=
  @UninitInvalid.mk T (typed T nonZero) rfl

instance default.instUninitInvalid {T : Type} : @UninitInvalid T Pointee.default :=
  typed.instUninitInvalid

instance Option.instLawful {T : Type} [Pointee T] : Lawful (Option T) := typed.lawful _ _
instance RawPtr.instLawful {T : Type} {M : Mutability} : Lawful (RawPtr T M) := typed.lawful _ _
instance Char.instLawful : Lawful Char := typed.lawful _ _
instance Option.instUninitInvalid {T : Type} [Pointee T] : UninitInvalid (Option T) :=
  typed.instUninitInvalid
instance RawPtr.instUninitInvalid {T : Type} {M : Mutability} : UninitInvalid (RawPtr T M) :=
  typed.instUninitInvalid

@[simp] theorem size_typed (T : Type) (nonZero : Bool) : @size T (typed T nonZero) = 1 := rfl
@[simp] theorem align_typed (T : Type) (nonZero : Bool) : @align T (typed T nonZero) = 1 := rfl
@[simp] theorem nonZero_typed (T : Type) (nonZero : Bool) :
    @Pointee.nonZero T (typed T nonZero) = nonZero := rfl
@[simp] theorem toCells_typed (T : Type) (nonZero : Bool) (value : T) :
    @toCells T (typed T nonZero) value = [some ⟨value⟩] := rfl
@[simp] theorem size_default (T : Type) : @size T Pointee.default = 1 := rfl
@[simp] theorem align_default (T : Type) : @align T Pointee.default = 1 := rfl
@[simp] theorem nonZero_default (T : Type) : @Pointee.nonZero T Pointee.default = false := rfl
@[simp] theorem toCells_default (T : Type) (value : T) :
    @toCells T Pointee.default value = [some ⟨value⟩] := rfl

theorem _root_.List.mapM_id_map_some {α : Type} (xs : List α) :
    (xs.map some).mapM id = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

theorem bytes.lawful (T : Type) (size align : Nat) (encode : T → List U8)
    (decode : List U8 → Option T) (length_encode : ∀ value, (encode value).length = size)
    (decode_encode : ∀ value, decode (encode value) = some value) (align_pos : 0 < align)
    (align_dvd_size : align ∣ size) : @Lawful T (bytes T size align encode decode) :=
  @Lawful.mk T (bytes T size align encode decode)
    (fun value => by
      show ((encode value).map some).length = size
      simp [length_encode])
    (fun value => by
      show ((encode value).map some).mapM id >>= decode = some value
      rw [List.mapM_id_map_some]
      exact decode_encode value)
    align_pos align_dvd_size

theorem bytes.uninitInvalid (T : Type) (size align : Nat) (encode : T → List U8)
    (decode : List U8 → Option T) (hSize : size ≠ 0) :
    @UninitInvalid T (bytes T size align encode decode) :=
  @UninitInvalid.mk T (bytes T size align encode decode) (by
    obtain ⟨n, rfl⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
    show (List.replicate (n + 1) (none : Option U8)).mapM id >>= decode = none
    simp [List.replicate_succ, List.mapM_cons])

theorem _root_.Aeneas.Std.UScalarTy.numBits_mod_eight (ty : UScalarTy) : ty.numBits % 8 = 0 := by
  cases ty <;> simp only [UScalarTy.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem _root_.Aeneas.Std.IScalarTy.numBits_mod_eight (ty : IScalarTy) : ty.numBits % 8 = 0 := by
  cases ty <;> simp only [IScalarTy.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem _root_.Aeneas.Std.UScalarTy.numBits_div_eight_pos (ty : UScalarTy) :
    0 < ty.numBits / 8 := by
  cases ty <;> simp only [UScalarTy.numBits] <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [h]

theorem _root_.Aeneas.Std.IScalarTy.numBits_div_eight_pos (ty : IScalarTy) :
    0 < ty.numBits / 8 := by
  cases ty <;> simp only [IScalarTy.numBits] <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [h]

theorem decodeLE_toLEBytes {n : Nat} (hn : n % 8 = 0) (b : BitVec n) :
    decodeLE n (b.toLEBytes.map UScalar.mk) = some b := by
  have hLen : 8 * (b.toLEBytes.map (UScalar.mk (ty := .U8))).length = n := by
    rw [List.length_map, BitVec.toLEBytes_length]; omega
  unfold decodeLE
  rw [dif_pos hLen]
  have hMap : (b.toLEBytes.map (UScalar.mk (ty := .U8))).map U8.bv = b.toLEBytes := by
    rw [List.map_map]; exact List.map_id _
  have key : ∀ l, l = b.toLEBytes → (BitVec.fromLEBytes l).toNat = b.toNat := by
    rintro l rfl
    rw [BitVec.fromLEBytes_toLEBytes hn, BitVec.toNat_cast]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast]
  exact key _ hMap

instance UScalar.instLawful (ty : UScalarTy) : Lawful (UScalar ty) :=
  bytes.lawful _ _ _ _ _
    (fun x => by
      rw [List.length_map, BitVec.toLEBytes_length]; have := ty.numBits_mod_eight; omega)
    (fun x => by simp only [decodeLE_toLEBytes ty.numBits_mod_eight, Option.map_some])
    ty.numBits_div_eight_pos (Nat.dvd_refl _)

instance IScalar.instLawful (ty : IScalarTy) : Lawful (IScalar ty) :=
  bytes.lawful _ _ _ _ _
    (fun x => by
      rw [List.length_map, BitVec.toLEBytes_length]; have := ty.numBits_mod_eight; omega)
    (fun x => by simp only [decodeLE_toLEBytes ty.numBits_mod_eight, Option.map_some])
    ty.numBits_div_eight_pos (Nat.dvd_refl _)

instance Bool.instLawful : Lawful Bool :=
  bytes.lawful _ _ _ _ _ (fun _ => rfl) (fun b => by cases b <;> rfl) Nat.one_pos (Nat.dvd_refl 1)

instance UScalar.instUninitInvalid (ty : UScalarTy) : UninitInvalid (UScalar ty) :=
  bytes.uninitInvalid _ _ _ _ _ (Nat.pos_iff_ne_zero.mp ty.numBits_div_eight_pos)

instance IScalar.instUninitInvalid (ty : IScalarTy) : UninitInvalid (IScalar ty) :=
  bytes.uninitInvalid _ _ _ _ _ (Nat.pos_iff_ne_zero.mp ty.numBits_div_eight_pos)

instance Bool.instUninitInvalid : UninitInvalid Bool := bytes.uninitInvalid _ _ _ _ _ (by decide)

@[simp] theorem size_uscalar (ty : UScalarTy) : size (UScalar ty) = ty.numBits / 8 := rfl
@[simp] theorem align_uscalar (ty : UScalarTy) : align (UScalar ty) = ty.numBits / 8 := rfl
@[simp] theorem size_iscalar (ty : IScalarTy) : size (IScalar ty) = ty.numBits / 8 := rfl
@[simp] theorem align_iscalar (ty : IScalarTy) : align (IScalar ty) = ty.numBits / 8 := rfl
@[simp] theorem size_bool : size Bool = 1 := rfl
@[simp] theorem align_bool : align Bool = 1 := rfl
@[simp] theorem nonZero_uscalar (ty : UScalarTy) : Pointee.nonZero (UScalar ty) = true := by
  show (ty.numBits / 8 != 0) = true
  simp [Nat.pos_iff_ne_zero.mp ty.numBits_div_eight_pos]
@[simp] theorem nonZero_iscalar (ty : IScalarTy) : Pointee.nonZero (IScalar ty) = true := by
  show (ty.numBits / 8 != 0) = true
  simp [Nat.pos_iff_ne_zero.mp ty.numBits_div_eight_pos]
@[simp] theorem nonZero_bool : Pointee.nonZero Bool = true := rfl
@[simp] theorem toCells_uscalar {ty : UScalarTy} (x : UScalar ty) :
    toCells x = (x.bv.toLEBytes.map (UScalar.mk (ty := .U8))).map some := rfl
@[simp] theorem toCells_u8 (x : U8) : toCells x = [some x] := by
  simp only [toCells_uscalar]
  have h : x.bv.toLEBytes = [x.bv] := by
    unfold BitVec.toLEBytes
    simp only [gt_iff_lt, Nat.ofNat_pos, ↓reduceIte]
    unfold BitVec.toLEBytes
    simp
  rw [h]
  rfl

theorem length_flatMap_toCells {T : Type} [Pointee T] [Lawful T] (values : List T) :
    (values.flatMap toCells).length = values.length * size T := by
  induction values with
  | nil => simp
  | cons value values ih =>
    simp [List.flatMap_cons, Lawful.length_toCells, ih, Nat.succ_mul, Nat.add_comm]

theorem length_optCells {T : Type} [Pointee T] [Lawful T] (content : Option T) :
    (optCells content).length = size T := by
  cases content <;> simp [optCells, Lawful.length_toCells]

theorem length_flatMap_optCells {T : Type} [Pointee T] [Lawful T] (contents : List (Option T)) :
    (contents.flatMap optCells).length = contents.length * size T := by
  induction contents with
  | nil => simp
  | cons content contents ih =>
    simp [List.flatMap_cons, length_optCells, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem optCells_some {T : Type} [Pointee T] (value : T) :
    optCells (some value) = toCells value := rfl

@[simp] theorem optCells_none {T : Type} [Pointee T] :
    optCells (none : Option T) = List.replicate (size T) none := rfl

theorem flatMap_optCells_map_some {T : Type} [Pointee T] (values : List T) :
    (values.map some).flatMap optCells = values.flatMap toCells := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.flatMap_cons, ih]

theorem ofCellsList_flatMap {T : Type} [Pointee T] [Lawful T] (values : List T)
    (rest : List (Option (Cell T))) :
    ofCellsList T values.length (values.flatMap toCells ++ rest) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.length_cons, ofCellsList, List.flatMap_cons, List.append_assoc]
    rw [List.take_left' (Lawful.length_toCells value),
      List.drop_left' (Lawful.length_toCells value), Lawful.ofCells_toCells, ih]
    rfl

instance Array.instLawful {T : Type} [Pointee T] [Lawful T] {n : Usize} : Lawful (Array T n) where
  length_toCells a := by
    simp only [Pointee.toCells, Pointee.size, length_flatMap_toCells, Array.property]
  ofCells_toCells a := by
    have h := ofCellsList_flatMap a.val []
    rw [List.append_nil, Array.property] at h
    simp only [Pointee.toCells, Pointee.ofCells, h, Option.bind_eq_bind, Option.bind_some,
      Array.property, dite_true, Array.val_from]
  align_pos := (Lawful.align_pos : 0 < align T)
  align_dvd_size := Dvd.dvd.mul_left (Lawful.align_dvd_size : align T ∣ size T) _

@[simp] theorem size_array (T : Type) [Pointee T] (n : Usize) :
    size (Array T n) = n.val * size T := rfl
@[simp] theorem align_array (T : Type) [Pointee T] (n : Usize) :
    align (Array T n) = align T := rfl

end Pointee

/-! ### Cells -/

open WP

namespace HeapOp

variable {α : Type}

theorem owns_array_cons (l : Loc) (content : Option α) (rest : List (Option α)) :
    owns (Heap.array l (content :: rest)) =
      iprop(owns (Heap.cell (⟨l⟩ : MutRawPtr α) content) ∗ owns (Heap.array (l.shift 1) rest)) := by
  have hCompatible := Heap.compatible_array_append l [content] rest
  rw [Heap.array_singleton, List.length_singleton] at hCompatible
  rw [Heap.array_cons]
  exact owns_union _ _ hCompatible

theorem owns_array_append (l : Loc) (xs ys : List (Option α)) :
    owns (Heap.array l (xs ++ ys)) =
      iprop(owns (Heap.array l xs) ∗ owns (Heap.array (l.shift xs.length) ys)) := by
  rw [Heap.array_append]
  exact owns_union _ _ (Heap.compatible_array_append l xs ys)

@[simp] theorem owns_array_nil (l : Loc) : owns (Heap.array l ([] : List (Option α))) = emp :=
  entails_antisymm (fun _ _ => trivial) fun h _ => by
    rw [Heap.array_nil]
    exact Heap.Subheap.of_empty h

@[simp] theorem borrowedAt_zero (l : Loc) : borrowedAt l 0 = emp := rfl

theorem borrowedAt_succ (l : Loc) (n : Nat) :
    borrowedAt l (n + 1) = iprop(owns (Heap.borrowedSlot l) ∗ borrowedAt (l.shift 1) n) := rfl

theorem borrowedAt_add (l : Loc) (m n : Nat) :
    borrowedAt l (m + n) = iprop(borrowedAt l m ∗ borrowedAt (l.shift m) n) := by
  induction m generalizing l with
  | zero => simp [sep_emp_l_eq]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, borrowedAt_succ, ih, borrowedAt_succ, sep_assoc_eq,
      Loc.shift_shift, Nat.add_comm 1 m]

theorem isValid_of_array {l : Loc} {contents : List (Option α)} {h : Heap}
    (hCells : owns (Heap.array l contents) h) {i : Nat} (hi : i < contents.length) :
    Heap.IsValid h (⟨l.shift i⟩ : MutRawPtr α) :=
  Heap.Subheap.isValid hCells (Heap.isValid_array hi)

theorem live_of_array {l : Loc} {contents : List (Option α)} {h : Heap}
    (hCells : owns (Heap.array l contents) h) {n : Nat} (hn : n ≤ contents.length) : Live α h l n :=
  fun _ hi => isValid_of_array hCells (by omega)

theorem read.spec (l : Loc) (content : Option α) :
    ⦃ owns (Heap.cell (⟨l⟩ : MutRawPtr α) content) ⦄ read α l
      ⦃ result => ⌜result = content⌝ ∗ owns (Heap.cell (⟨l⟩ : MutRawPtr α) content) ⦄ := by
  apply ispec_guardedModify
  intro h hCell frame hCompatible
  have hSub : Heap.Subheap (Heap.cell (⟨l⟩ : MutRawPtr α) content) (h ∪ frame) :=
    (show Heap.Subheap _ h from hCell).trans (Heap.Subheap.union_left hCompatible)
  exact ⟨hSub.isValid (Heap.isValid_cell _ content), h, hCompatible, rfl,
    (sep_pure_l _ _ h).mpr ⟨Heap.read_of_subheap hSub _, hCell⟩⟩

theorem write.spec (l : Loc) (content newContent : Option α) :
    ⦃ owns (Heap.cell (⟨l⟩ : MutRawPtr α) content) ⦄ write l newContent
      ⦃ owns (Heap.cell (⟨l⟩ : MutRawPtr α) newContent) ⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hPointsTo
  have hContainsSlot := Heap.isValid_cell (⟨l⟩ : MutRawPtr α) content
  have hContains : Heap.IsValid (Heap.cell (⟨l⟩ : MutRawPtr α) content ∪ rest) (⟨l⟩ : MutRawPtr α) :=
    Heap.isValid_union_left hContainsSlot
  refine ⟨Heap.isValid_union_left hContains,
    (Heap.write (⟨l⟩ : MutRawPtr α) newContent _ hContains).2,
    Heap.compatible_write_left hCompatible hContains, ?_, ?_⟩
  · exact congrArg Prod.snd
      (Heap.write_union_left (h₂ := frame) (⟨l⟩ : MutRawPtr α) newContent hContains)
  · have hCompatibleNew :
        PartialCommMonoid.Compatible (Heap.cell (⟨l⟩ : MutRawPtr α) newContent) rest := by
      have hUpdated := Heap.compatible_write_left (value := newContent)
        hCompatibleRest hContainsSlot
      rwa [Heap.write_cell] at hUpdated
    rw [show hContains = Heap.isValid_union_left hContainsSlot from
      Subsingleton.elim _ _, Heap.write_union_left (⟨l⟩ : MutRawPtr α) _ hContainsSlot]
    simp only [Prod.map_snd, Heap.write_cell]
    exact Heap.Subheap.union_left hCompatibleNew

theorem borrow.spec (l : Loc) (content : Option α) :
    ⦃ owns (Heap.cell (⟨l⟩ : MutRawPtr α) content) ⦄ borrow α l
      ⦃ result => ⌜result = content⌝ ∗ owns (Heap.borrowedSlot l) ⦄ := by
  apply ispec_guardedModify
  intro h hCell frame hCompatible
  have hSubFrame : Heap.Subheap (Heap.cell (⟨l⟩ : MutRawPtr α) content) (h ∪ frame) :=
    (show Heap.Subheap _ h from hCell).trans (Heap.Subheap.union_left hCompatible)
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hCell
  have hSlot := Heap.isValid_cell (⟨l⟩ : MutRawPtr α) content
  have hValid : Heap.IsValid (Heap.cell (⟨l⟩ : MutRawPtr α) content ∪ rest) (⟨l⟩ : MutRawPtr α) :=
    Heap.isValid_union_left hSlot
  refine ⟨Heap.isValid_union_left hValid, (Heap.borrow (⟨l⟩ : MutRawPtr α) _ hValid).2,
    Heap.compatible_borrow_left hCompatible hValid, ?_, ?_⟩
  · exact congrArg Prod.snd (Heap.borrow_union_left (h₂ := frame) (⟨l⟩ : MutRawPtr α) hValid)
  · have hBorrowedRest : PartialCommMonoid.Compatible (Heap.borrowedSlot l) rest := by
      have hBorrowed := Heap.compatible_borrow_left hCompatibleRest hSlot
      rwa [Heap.borrow_cell] at hBorrowed
    refine (sep_pure_l _ _ _).mpr
      ⟨(Heap.borrow_fst _).trans (Heap.read_of_subheap hSubFrame _), ?_⟩
    rw [show hValid = Heap.isValid_union_left hSlot from Subsingleton.elim _ _,
      Heap.borrow_union_left (⟨l⟩ : MutRawPtr α) hSlot]
    simp only [Prod.map_snd, Heap.borrow_cell]
    exact Heap.Subheap.union_left hBorrowedRest

theorem endBorrow.spec (l : Loc) (content : Option α) :
    ⦃ owns (Heap.borrowedSlot l) ⦄ endBorrow l content
      ⦃ owns (Heap.cell (⟨l⟩ : MutRawPtr α) content) ⦄ := by
  apply ispec_guardedModify
  intro h hBorrowedSub frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := Heap.subheap_iff.mp hBorrowedSub
  have hSlot : Heap.IsBorrowed (Heap.borrowedSlot l) (⟨l⟩ : MutRawPtr α).loc :=
    Heap.isBorrowed_borrowedSlot l
  have hBorrowed : Heap.IsBorrowed (Heap.borrowedSlot l ∪ rest) (⟨l⟩ : MutRawPtr α).loc :=
    Heap.isBorrowed_union_left hSlot
  refine ⟨Heap.isBorrowed_union_left hBorrowed,
    (Heap.endBorrow (⟨l⟩ : MutRawPtr α) content _ hBorrowed).2,
    Heap.compatible_endBorrow_left hCompatible hBorrowed, ?_, ?_⟩
  · exact congrArg Prod.snd
      (Heap.endBorrow_union_left (h₂ := frame) (⟨l⟩ : MutRawPtr α) content hBorrowed)
  · have hLiveRest :
        PartialCommMonoid.Compatible (Heap.cell (⟨l⟩ : MutRawPtr α) content) rest := by
      have hLive := Heap.compatible_endBorrow_left (value := content) (q := (⟨l⟩ : MutRawPtr α))
        hCompatibleRest hSlot
      rwa [Heap.endBorrow_borrowedSlot] at hLive
    show Heap.Subheap _ _
    rw [show hBorrowed = Heap.isBorrowed_union_left hSlot from Subsingleton.elim _ _,
      Heap.endBorrow_union_left (⟨l⟩ : MutRawPtr α) _ hSlot]
    rw [Prod.map_snd, Heap.endBorrow_borrowedSlot (⟨l⟩ : MutRawPtr α)]
    exact Heap.Subheap.union_left hLiveRest

theorem reads.spec (l : Loc) (contents : List (Option α)) :
    ⦃ owns (Heap.array l contents) ⦄ reads α l contents.length
      ⦃ result => ⌜result = contents⌝ ∗ owns (Heap.array l contents) ⦄ := by
  induction contents generalizing l with
  | nil => rw [owns_array_nil]; simp [reads]
  | cons content contents ih =>
    rw [owns_array_cons, List.length_cons, reads]
    apply ispec_bind (read.spec l content)
    · iframe
    · intro c
      rw [sep_assoc_eq, ispec_ipure]
      rintro rfl
      apply ispec_bind (ih (l.shift 1))
      · iframe
      · intro cs
        rw [sep_assoc_eq, ispec_ipure]
        rintro rfl
        apply (ispec_ok _).2
        iframe

theorem writes.spec (l : Loc) (contents newContents : List (Option α))
    (hLen : newContents.length = contents.length) :
    ⦃ owns (Heap.array l contents) ⦄ writes l newContents ⦃ owns (Heap.array l newContents) ⦄ := by
  induction contents generalizing l newContents with
  | nil =>
    have : newContents = [] := List.length_eq_zero_iff.mp (by simpa using hLen)
    subst this
    rw [owns_array_nil]
    simp [writes]
  | cons content contents ih =>
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_length_pos (l := newContents) (by simp [hLen])
    rw [owns_array_cons, owns_array_cons, writes]
    apply ispec_bind (write.spec l content c)
    · iframe
    · intro _
      apply ispec_mono (ih (l.shift 1) cs (by simpa using hLen)) <;> iframe

theorem borrows.spec (l : Loc) (contents : List (Option α)) :
    ⦃ owns (Heap.array l contents) ⦄ borrows α l contents.length
      ⦃ result => ⌜result = contents⌝ ∗ borrowedAt l contents.length ⦄ := by
  induction contents generalizing l with
  | nil => simp [borrows]
  | cons content contents ih =>
    rw [owns_array_cons, List.length_cons, borrows, borrowedAt_succ]
    apply ispec_bind (borrow.spec l content)
    · iframe
    · intro c
      rw [sep_assoc_eq, ispec_ipure]
      rintro rfl
      apply ispec_bind (ih (l.shift 1))
      · iframe
      · intro cs
        rw [sep_assoc_eq, ispec_ipure]
        rintro rfl
        apply (ispec_ok _).2
        iframe

theorem endBorrows.spec (l : Loc) (contents : List (Option α)) :
    ⦃ borrowedAt l contents.length ⦄ endBorrows l contents ⦃ owns (Heap.array l contents) ⦄ := by
  induction contents generalizing l with
  | nil => rw [owns_array_nil]; simp [endBorrows]
  | cons content contents ih =>
    rw [owns_array_cons, List.length_cons, endBorrows, borrowedAt_succ]
    apply ispec_bind (endBorrow.spec l content)
    · iframe
    · intro _
      apply ispec_mono (ih (l.shift 1)) <;> iframe

/-- An access to the cell at `l` fails if the slot at `l` is owned and holds no value. -/
theorem ifails_of_not_isLive {β : Type} {A : Heap} {l : Loc}
    (hNotLive : ∀ h, Heap.Subheap A h → ¬ Heap.IsLive h l)
    {f : (h : Heap) → Heap.IsValid h (⟨l⟩ : MutRawPtr α) → β × Heap} :
    ifails (owns A) (Result.guardedModify _ f) := by
  apply ifails_guardedModify
  intro h hA h' hSub hValid
  exact hNotLive h' (Heap.Subheap.trans hA hSub) (Heap.isLive_of_isValid hValid)

theorem not_isLive_of_borrowedSlot {l : Loc} :
    ∀ h, Heap.Subheap (Heap.borrowedSlot l) h → ¬ Heap.IsLive h l :=
  fun _ hSub => Heap.not_isLive_of_isBorrowed (Heap.Subheap.isBorrowed hSub)

theorem read.fails_borrowed (α : Type) (l : Loc) :
    ifails (owns (Heap.borrowedSlot l)) (read α l) :=
  ifails_of_not_isLive not_isLive_of_borrowedSlot

theorem borrow.fails_borrowed (α : Type) (l : Loc) :
    ifails (owns (Heap.borrowedSlot l)) (borrow α l) :=
  ifails_of_not_isLive not_isLive_of_borrowedSlot

theorem write.fails_borrowed {α : Type} (l : Loc) (content : Option α) :
    ifails (owns (Heap.borrowedSlot l)) (write l content) :=
  ifails_of_not_isLive not_isLive_of_borrowedSlot

theorem read.fails_freed (α : Type) (l : Loc) : ifails (owns (Heap.freedSlot l)) (read α l) :=
  ifails_of_not_isLive fun _ hSub => Heap.not_isLive_of_isFreed (Heap.Subheap.isFreed hSub)

theorem read.fails_end (α : Type) (l : Loc) (kind : AllocKind) :
    ifails (owns (Heap.endMarker l kind)) (read α l) :=
  ifails_of_not_isLive fun _ hSub => Heap.not_isLive_of_isEndMarker (Heap.Subheap.isEndMarker hSub)

/-- Reading `n > 0` cells starting with a borrowed one fails. -/
theorem reads.fails_borrowed (α : Type) (l : Loc) (n : Nat) (hn : 0 < n) :
    ifails (owns (Heap.borrowedSlot l)) (reads α l n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [reads]
  exact ifails_bind_left (read.fails_borrowed α l)

theorem reads.fails_freed (α : Type) (l : Loc) (n : Nat) (hn : 0 < n) :
    ifails (owns (Heap.freedSlot l)) (reads α l n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [reads]
  exact ifails_bind_left (read.fails_freed α l)

theorem reads.fails_end (α : Type) (l : Loc) (kind : AllocKind) (n : Nat) (hn : 0 < n) :
    ifails (owns (Heap.endMarker l kind)) (reads α l n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [reads]
  exact ifails_bind_left (read.fails_end α l kind)

theorem borrows.fails_borrowed (α : Type) (l : Loc) (n : Nat) (hn : 0 < n) :
    ifails (owns (Heap.borrowedSlot l)) (borrows α l n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [borrows]
  exact ifails_bind_left (borrow.fails_borrowed α l)

theorem writes.fails_borrowed {α : Type} (l : Loc) (contents : List (Option α))
    (hn : 0 < contents.length) : ifails (owns (Heap.borrowedSlot l)) (writes l contents) := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_length_pos hn
  rw [writes]
  exact ifails_bind_left (write.fails_borrowed l c)

end HeapOp

/-! ### Pointers -/

namespace RawPtr

@[simp] theorem shiftCells_zero (q : RawPtr T M) : q.shiftCells 0 = q :=
  RawPtr.ext (by simp)
theorem shiftCells_shiftCells (q : RawPtr T M) (i j : Nat) :
    (q.shiftCells i).shiftCells j = q.shiftCells (i + j) :=
  RawPtr.ext (by simp [Loc.shift_shift])

section

variable {T : Type} [Pointee T] {M : Mutability}

@[simp] theorem loc_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).loc = q.loc.shift (i * Pointee.size T) := by
  simp [shift]
@[simp] theorem shift_zero (q : RawPtr T M) : q.shift 0 = q := by simp [shift]
theorem shift_shift (q : RawPtr T M) (i j : Nat) : (q.shift i).shift j = q.shift (i + j) := by
  simp [shift, shiftCells_shiftCells, Nat.add_mul]

theorem shift_eq_shiftCells (q : RawPtr T M) (i : Nat) :
    q.shift i = q.shiftCells (i * Pointee.size T) := rfl

@[simp] theorem cellPtr_loc (q : RawPtr T M) : q.cellPtr.loc = q.loc := rfl

end

@[simp] theorem loc_cast (q : RawPtr T M) (U : Type _) : (q.cast U).loc = q.loc := rfl

@[simp] theorem cast_cast (q : RawPtr T M) (U V : Type _) : (q.cast U).cast V = q.cast V := rfl

@[simp] theorem cast_self (q : RawPtr T M) : q.cast T = q := rfl

@[simp] theorem shiftCells_cast (q : RawPtr T M) (U : Type _) (i : Nat) :
    (q.cast U).shiftCells i = (q.shiftCells i).cast U := RawPtr.ext (by simp)

@[simp] theorem loc_cast_const (q : MutRawPtr T) : q.cast_const.loc = q.loc := rfl

theorem ext_loc {q r : RawPtr T M} (hEq : q.loc = r.loc) : q = r := RawPtr.ext hEq

end RawPtr

section PointsTo

variable {T : Type} [Pointee T] {M : Mutability}

namespace RawPtr

theorem pointsTo_eq (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦# Pointee.toCells value) := rfl

theorem pointsToRange_eq_cells (q : RawPtr T M) (values : List T) :
    (q ↦* values) = (q ↦# values.flatMap Pointee.toCells) := rfl

theorem pointsToOpt_eq (q : RawPtr T M) (content : Option T) :
    (q ↦? content) = (q ↦# Pointee.optCells content) := rfl

theorem pointsToOpts_eq (q : RawPtr T M) (contents : List (Option T)) :
    (q ↦*? contents) = (q ↦# contents.flatMap Pointee.optCells) := rfl

@[simp] theorem pointsToOpt_some (q : RawPtr T M) (value : T) :
    (q ↦? some value) = (q ↦ value) := rfl

theorem pointsToRange_eq (q : RawPtr T M) (values : List T) :
    (q ↦* values) = (q ↦*? values.map some) := by
  rw [pointsToOpts_eq, Pointee.flatMap_optCells_map_some]
  rfl

theorem pointsToCells_eq_array (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) :
    (q ↦# cells) = owns (Heap.array q.loc cells) := rfl

@[simp] theorem pointsTo_cast_const (q : MutRawPtr T) (value : T) :
    (q.cast_const ↦ value) = (q ↦ value) := rfl
@[simp] theorem pointsToRange_cast_const (q : MutRawPtr T) (values : List T) :
    (q.cast_const ↦* values) = (q ↦* values) := rfl
@[simp] theorem pointsToOpt_cast_const (q : MutRawPtr T) (content : Option T) :
    (q.cast_const ↦? content) = (q ↦? content) := rfl
@[simp] theorem pointsToOpts_cast_const (q : MutRawPtr T) (contents : List (Option T)) :
    (q.cast_const ↦*? contents) = (q ↦*? contents) := rfl
@[simp] theorem pointsToCells_cast_const (q : MutRawPtr T)
    (cells : List (Option (Pointee.Cell T))) : (q.cast_const ↦# cells) = (q ↦# cells) := rfl
@[simp] theorem pointsToBorrowed_cast_const (q : MutRawPtr T) (n : Nat) :
    (q.cast_const ↦† n) = (q ↦† n) := rfl

@[simp] theorem pointsToCells_nil (q : RawPtr T M) :
    (q ↦# ([] : List (Option (Pointee.Cell T)))) = emp := HeapOp.owns_array_nil _

theorem pointsToCells_append (q : RawPtr T M) (xs ys : List (Option (Pointee.Cell T))) :
    (q ↦# (xs ++ ys)) = iprop(q ↦# xs ∗ (q.shiftCells xs.length) ↦# ys) := by
  simp only [pointsToCells_eq_array, loc_shiftCells]
  exact HeapOp.owns_array_append _ _ _

@[simp] theorem pointsToRange_nil (q : RawPtr T M) : (q ↦* ([] : List T)) = emp :=
  pointsToCells_nil q

@[simp] theorem pointsToOpts_nil (q : RawPtr T M) : (q ↦*? ([] : List (Option T))) = emp :=
  pointsToCells_nil q

variable [Pointee.Lawful T]

theorem pointsToRange_append (q : RawPtr T M) (xs ys : List T) :
    (q ↦* (xs ++ ys)) = iprop(q ↦* xs ∗ (q.shift xs.length) ↦* ys) := by
  rw [pointsToRange_eq_cells, List.flatMap_append, pointsToCells_append,
    Pointee.length_flatMap_toCells]
  rfl

theorem pointsToRange_cons (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.shift 1) ↦* rest) := by
  rw [pointsToRange_eq_cells, List.flatMap_cons, pointsToCells_append,
    Pointee.Lawful.length_toCells, shift_eq_shiftCells, Nat.one_mul]
  rfl

theorem pointsTo_eq_range (q : RawPtr T M) (value : T) : (q ↦ value) = (q ↦* [value]) := by
  rw [pointsToRange_cons, pointsToRange_nil, sep_emp_r_eq]

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
  rw [pointsToRange_split q values i, hTake, List.drop_eq_getElem_cons hIndex,
    pointsToRange_cons, shift_shift]

theorem pointsToOpts_append (q : RawPtr T M) (xs ys : List (Option T)) :
    (q ↦*? (xs ++ ys)) = iprop(q ↦*? xs ∗ (q.shift xs.length) ↦*? ys) := by
  rw [pointsToOpts_eq, List.flatMap_append, pointsToCells_append,
    Pointee.length_flatMap_optCells]
  rfl

theorem pointsToOpts_cons (q : RawPtr T M) (content : Option T) (rest : List (Option T)) :
    (q ↦*? (content :: rest)) = iprop(q ↦? content ∗ (q.shift 1) ↦*? rest) := by
  rw [pointsToOpts_eq, List.flatMap_cons, pointsToCells_append, Pointee.length_optCells,
    shift_eq_shiftCells, Nat.one_mul]
  rfl

theorem pointsToOpt_eq_opts (q : RawPtr T M) (content : Option T) :
    (q ↦? content) = (q ↦*? [content]) := by
  rw [pointsToOpts_cons, pointsToOpts_nil, sep_emp_r_eq]

theorem pointsToOpts_split (q : RawPtr T M) (contents : List (Option T)) (i : Nat) :
    (q ↦*? contents) =
      iprop(q ↦*? contents.take i ∗ (q.shift (contents.take i).length) ↦*? contents.drop i) := by
  conv_lhs => rw [← List.take_append_drop i contents]
  exact pointsToOpts_append q (contents.take i) (contents.drop i)

theorem pointsToOpts_eq_take_get_drop {q : RawPtr T M} {contents : List (Option T)} {i : Nat}
    (hIndex : i < contents.length) :
    (q ↦*? contents) =
      iprop(q ↦*? contents.take i ∗
        ((q.shift i) ↦? contents[i] ∗ (q.shift (i + 1)) ↦*? contents.drop (i + 1))) := by
  have hTake : (contents.take i).length = i := by simp; omega
  rw [pointsToOpts_split q contents i, hTake, List.drop_eq_getElem_cons hIndex,
    pointsToOpts_cons, shift_shift]

end RawPtr

end PointsTo

namespace RawPtr

variable {T : Type} [Pointee T] {M : Mutability}

@[simp] theorem pointsToBorrowed_zero (q : RawPtr T M) : (q ↦† 0) = emp := by
  simp [pointsToBorrowed]

theorem pointsToBorrowed_add (q : RawPtr T M) (m n : Nat) :
    (q ↦† (m + n)) = iprop(q ↦† m ∗ (q.shift m) ↦† n) := by
  simp only [pointsToBorrowed, Nat.add_mul, HeapOp.borrowedAt_add, loc_shift]

theorem pointsToBorrowed_succ (q : RawPtr T M) (n : Nat) :
    (q ↦† (n + 1)) = iprop(q ↦† 1 ∗ (q.shift 1) ↦† n) := by
  rw [Nat.add_comm, pointsToBorrowed_add]

theorem pointsToBorrowed_one (q : RawPtr T M) :
    (q ↦† 1) = HeapOp.borrowedAt q.loc (Pointee.size T) := by
  simp [pointsToBorrowed]

theorem freeable_holds {count : Nat} {kind : AllocKind} (q : RawPtr T M) (h : Heap) :
    q.freeable count kind h ↔
      q.loc.offset = 0 ∧
        Heap.Subheap (Heap.endMarker (q.loc.shift (count * Pointee.size T)) kind) h :=
  Iff.rfl

@[simp] theorem freeable_cast_const (q : MutRawPtr T) (count : Nat) (kind : AllocKind) :
    q.cast_const.freeable count kind = q.freeable count kind := rfl

/-- The right to deallocate does not depend on the pointee, if the size does not change. -/
theorem freeable_cast {U : Type} [Pointee U] (q : RawPtr T M) (count : Nat) (kind : AllocKind)
    (hSize : Pointee.size U = Pointee.size T) :
    (q.cast U).freeable count kind = q.freeable count kind := by
  unfold freeable
  simp only [loc_cast, hSize]

/-! #### Alignment -/

omit [Pointee T] in
@[simp] theorem notNull_iff (q : RawPtr T M) (n : Nat) :
    q.NotNull n ↔ (n = 0 → q.loc.allocId ≠ 0) :=
  Iff.rfl

omit [Pointee T] in
/-- An access to some cells need not check the pointer (see `NotNull`). -/
theorem notNull_of_pos {q : RawPtr T M} {n : Nat} (h : 0 < n) : q.NotNull n :=
  fun h0 => absurd h0 (by omega)

@[simp] theorem aligned_iff (q : RawPtr T M) :
    q.Aligned ↔ Pointee.align T ∣ q.loc.allocId ∧ Pointee.align T ∣ q.loc.offset ∧
      (Pointee.size T = 0 → q.loc.allocId ≠ 0) := Iff.rfl

theorem Aligned.notNull {q : RawPtr T M} (hAligned : q.Aligned) : q.NotNull (Pointee.size T) :=
  hAligned.2.2

theorem NotNull.shift {q : RawPtr T M} {n : Nat} (hNotNull : q.NotNull n) (i : Nat) :
    (q.shift i).NotNull n := by
  simpa using hNotNull

theorem Aligned.shift [Pointee.Lawful T] {q : RawPtr T M} (hAligned : q.Aligned) (i : Nat) :
    (q.shift i).Aligned := by
  obtain ⟨h1, h2, h3⟩ := hAligned
  refine ⟨by simpa using h1, ?_, h3.shift i⟩
  simp only [loc_shift, Loc.offset_shift]
  exact Nat.dvd_add h2 (Dvd.dvd.mul_left Pointee.Lawful.align_dvd_size _)

@[simp] theorem aligned_cast_const (q : MutRawPtr T) : q.cast_const.Aligned ↔ q.Aligned := Iff.rfl

theorem Aligned.cast_const {q : MutRawPtr T} (hAligned : q.Aligned) : q.cast_const.Aligned :=
  hAligned

theorem aligned_of_align_one {q : RawPtr T M} (h : Pointee.align T = 1)
    (hNotNull : q.NotNull (Pointee.size T)) : q.Aligned := by
  simp_all

theorem not_aligned_null (hSize : Pointee.size T = 0) :
    ¬ (RawPtr.null : RawPtr T M).Aligned := by
  simp [RawPtr.null, hSize]

end RawPtr

/-! ### Specifications -/

theorem Result.require.fails {p : Prop} (hp : ¬ p) {P : IPre} : ifails P (Result.require p) := by
  apply ifails_guardedModify
  intro _ _ _ _ h
  exact hp h

theorem ifails_require_bind {β : Type u} {p : Prop} {k : Unit → Result β} {P : IPre}
    (hk : ifails P (k ())) : ifails P (Aeneas.Std.bind (Result.require p) k) :=
  ifails_bind_check hk

namespace RawPtr

theorem take_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set, if_neg (show ¬ i = n by omega)]

theorem drop_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).drop (i + 1) = values.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_drop, List.getElem_set, if_neg (show ¬ i = i + 1 + n by omega)]

end RawPtr

@[step]
theorem Result.require.spec {p : Prop} (hp : p) : ⦃ emp ⦄ Result.require p ⦃ emp⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  exact ⟨hp, h, hCompatible, rfl, trivial⟩

section Specs

variable {T : Type} [Pointee T] [Pointee.Lawful T] {M : Mutability}

omit [Pointee.Lawful T] in
theorem Pointee.decode.spec {cells : List (Option (Pointee.Cell T))} {value : T}
    (hValue : Pointee.ofCells cells = some value) {P : IPre} :
    ⦃ P ⦄ Pointee.decode cells ⦃ r => ⌜r = value⌝ ∗ P ⦄ := by
  simp only [Pointee.decode, hValue]
  apply (ispec_ok _).2
  iframe

omit [Pointee.Lawful T] in
theorem Pointee.decode.fails {cells : List (Option (Pointee.Cell T))}
    (hNone : Pointee.ofCells cells = none) {P : IPre} : ifails P (Pointee.decode cells) := by
  simp only [Pointee.decode, hNone]
  exact ifails_fail _

theorem Heap.aligned_freshAllocId (h : Heap) :
    Pointee.align T ∣ Heap.freshAllocId h (Pointee.align T) := by
  have h := Heap.dvd_freshAllocId h (Pointee.align T)
  rwa [Nat.max_eq_left (Pointee.Lawful.align_pos (T := T))] at h

/-- A fresh allocation is aligned, and hands out its values and the right to deallocate it. -/
theorem RawPtr.alloc.spec (values : List T) (kind : AllocKind) :
    ⦃ emp ⦄ RawPtr.alloc values kind
      ⦃ q => ⌜q.Aligned⌝ ∗ q ↦* values ∗ q.freeable values.length kind⦄ := by
  unfold RawPtr.alloc
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.allocation (Heap.freshLoc (h ∪ frame) (Pointee.align T))
          (values.flatMap Pointee.toCells) kind)
        (h ∪ frame) :=
    Heap.compatible_freshLoc _ _ _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.allocation (Heap.freshLoc (h ∪ frame) (Pointee.align T))
        (values.flatMap Pointee.toCells) kind) h frame).mpr
        ⟨hCompatible, hFresh⟩
  refine ⟨trivial, _, hFreshFrame, ?_, ?_⟩
  · rw [Heap.alloc_eq]
    exact (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm
  · rw [Heap.alloc_eq]
    have hAllocation := Heap.Subheap.union_left (h₂ := h) hFreshH
    rw [Heap.allocation_eq] at hAllocation
    have hSplit : (owns (Heap.array (Heap.freshLoc (h ∪ frame) (Pointee.align T))
          (values.flatMap Pointee.toCells)) ∗
        owns (Heap.endMarker
          ((Heap.freshLoc (h ∪ frame) (Pointee.align T)).shift
            (values.flatMap Pointee.toCells).length) kind))
          (Heap.allocation (Heap.freshLoc (h ∪ frame) (Pointee.align T))
            (values.flatMap Pointee.toCells) kind ∪ h) := by
      rw [← owns_union _ _ (Heap.compatible_array_endMarker _ _ _), Heap.allocation_eq]
      exact hAllocation
    rw [Pointee.length_flatMap_toCells] at hSplit
    refine (sep_pure_l _ _ _).mpr ⟨?_, sep_mono (entails_refl _)
      (fun h' hEnd => (RawPtr.freeable_holds _ h').mpr ⟨Heap.freshLoc_offset _ _, hEnd⟩) _ hSplit⟩
    refine ⟨?_, ?_, fun _ => ?_⟩
    · rw [Heap.freshLoc_allocId]; exact Heap.aligned_freshAllocId _
    · rw [Heap.freshLoc_offset]; exact Nat.dvd_zero _
    · rw [Heap.freshLoc_allocId]; exact Heap.freshAllocId_ne_zero _ _

omit [Pointee.Lawful T] in
/-- Deallocating needs the cells and the right to deallocate them: without it, `q` could be an
interior pointer, or point to an allocation of another kind. The slot at `q` is then freed. -/
theorem Heap.dealloc.spec_freed (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (count : Nat) (kind : AllocKind) (hLen : cells.length = count * Pointee.size T) :
    ispec (q ↦# cells ∗ q.freeable count kind)
      (Result.guardedModify _ (Heap.dealloc q (count * Pointee.size T) kind))
      (fun _ => q.freed) := by
  apply ispec_guardedModify
  intro h hPre frame hCompatible
  have hRange : Heap.Subheap (Heap.array q.loc cells) h := sep_elim_right _ _ h hPre
  obtain ⟨hOffset, hEnd⟩ := (RawPtr.freeable_holds q h).mp (sep_elim_left _ _ h hPre)
  have hDealloc : Heap.CanDealloc h q (count * Pointee.size T) kind :=
    Heap.canDealloc_iff.mpr ⟨hOffset, fun _ hi => hRange.isLive (Heap.isLive_array (by omega)),
      Heap.Subheap.isEndMarker hEnd⟩
  exact ⟨Heap.canDealloc_union_left hDealloc, (h.dealloc q _ kind hDealloc).2,
    Heap.compatible_dealloc_left hCompatible hDealloc,
    congrArg Prod.snd (Heap.dealloc_union_left hDealloc),
    Heap.subheap_freedSlot (by simpa using Heap.isFreed_dealloc hDealloc (Nat.zero_le _))⟩

omit [Pointee.Lawful T] in
theorem Heap.dealloc.spec (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (count : Nat) (kind : AllocKind) (hLen : cells.length = count * Pointee.size T) :
    ispec (q ↦# cells ∗ q.freeable count kind)
      (Result.guardedModify _ (Heap.dealloc q (count * Pointee.size T) kind)) (fun _ => emp) :=
  WP.ispec_mono (Heap.dealloc.spec_freed q cells count kind hLen)
    (entails_of_eq (sep_emp_r_eq _).symm) (by iframe)

@[step]
theorem RawPtr.allocView.spec (values : List T) :
    ⦃ emp ⦄ RawPtr.allocView values
      ⦃ p => ⌜p.Aligned⌝ ∗ p ↦* values ∗ p.freeable values.length .view⦄ :=
  RawPtr.alloc.spec values .view

omit [Pointee.Lawful T] in
/-- Ending a view needs its cells, initialized or not. -/
theorem RawPtr.endView.spec_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (count : Nat) (hLen : cells.length = count * Pointee.size T) :
    ⦃ q ↦# cells ∗ q.freeable count .view ⦄ q.endView count ⦃ emp⦄ :=
  Heap.dealloc.spec q cells count .view hLen

@[step]
theorem RawPtr.endView.spec (q : RawPtr T M) (values : List T) (count : Nat)
    (hCount : values.length = count) :
    ⦃ q ↦* values ∗ q.freeable count .view ⦄ q.endView count ⦃ emp⦄ :=
  RawPtr.endView.spec_cells q _ count (by rw [Pointee.length_flatMap_toCells, hCount])

/-- Ending a view of values some of which may be uninitialized. -/
theorem RawPtr.endView.spec_opts (q : RawPtr T M) (contents : List (Option T)) (count : Nat)
    (hCount : contents.length = count) :
    ⦃ q ↦*? contents ∗ q.freeable count .view ⦄ q.endView count ⦃ emp⦄ :=
  RawPtr.endView.spec_cells q _ count (by rw [Pointee.length_flatMap_optCells, hCount])

namespace RawPtr

omit [Pointee.Lawful T] in
theorem load.spec_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) (value : T)
    (hLen : cells.length = Pointee.size T) (hValue : Pointee.ofCells cells = some value) :
    ⦃ q ↦# cells ⦄ q.load ⦃ r => ⌜r = value⌝ ∗ q ↦# cells ⦄ := by
  unfold RawPtr.load
  rw [← hLen]
  apply ispec_bind (HeapOp.reads.spec q.loc cells)
  · iframe
  · intro cs
    rw [sep_assoc_eq, ispec_ipure]
    rintro rfl
    apply WP.ispec_mono (Pointee.decode.spec hValue (P := emp)) <;> iframe

@[step]
theorem load.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.load ⦃ r => ⌜r = value⌝ ∗ q ↦ value ⦄ :=
  load.spec_cells q _ value (Pointee.Lawful.length_toCells value)
    (Pointee.Lawful.ofCells_toCells value)

omit [Pointee.Lawful T] in
theorem read_unaligned.spec_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (value : T) (hLen : cells.length = Pointee.size T)
    (hValue : Pointee.ofCells cells = some value) (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦# cells ⦄ q.read_unaligned ⦃ r => ⌜r = value⌝ ∗ q ↦# cells ⦄ := by
  unfold RawPtr.read_unaligned
  apply ispec_bind (Result.require.spec hNotNull)
  · iframe
  · intro _
    apply WP.ispec_mono (load.spec_cells q cells value hLen hValue) <;> iframe

@[step]
theorem read_unaligned.spec (q : RawPtr T M) (value : T) (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦ value ⦄ q.read_unaligned ⦃ r => ⌜r = value⌝ ∗ q ↦ value ⦄ :=
  read_unaligned.spec_cells q _ value (Pointee.Lawful.length_toCells value)
    (Pointee.Lawful.ofCells_toCells value) hNotNull

omit [Pointee.Lawful T] in
theorem read.spec_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (value : T) (hLen : cells.length = Pointee.size T)
    (hValue : Pointee.ofCells cells = some value) (hAlign : q.Aligned) :
    ⦃ q ↦# cells ⦄ q.read ⦃ r => ⌜r = value⌝ ∗ q ↦# cells ⦄ := by
  unfold RawPtr.read
  apply ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    apply WP.ispec_mono (read_unaligned.spec_cells q cells value hLen hValue hAlign.notNull) <;>
      iframe

/-- Reading a value which may be uninitialized needs it to be initialized. -/
theorem read.spec_opt (q : RawPtr T M) (value : T) (hAlign : q.Aligned) :
    ⦃ q ↦? some value ⦄ q.read ⦃ r => ⌜r = value⌝ ∗ q ↦? some value ⦄ :=
  read.spec_cells q _ value (Pointee.Lawful.length_toCells value)
    (Pointee.Lawful.ofCells_toCells value) hAlign

@[step]
theorem read.spec (q : RawPtr T M) (value : T) (hAlign : q.Aligned) :
    ⦃ q ↦ value ⦄ q.read ⦃ r => ⌜r = value⌝ ∗ q ↦ value ⦄ :=
  read.spec_cells q _ value (Pointee.Lawful.length_toCells value)
    (Pointee.Lawful.ofCells_toCells value) hAlign

theorem read.spec_frame (q : RawPtr T M) (value : T) (H : IProp)
    (hAlign : q.Aligned) :
    ⦃ q ↦ value ∗ H ⦄ q.read ⦃ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ := by
  apply WP.ispec_mono (read.spec q value hAlign) <;> iframe

theorem read.spec_range (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) (hAlign : q.Aligned) :
    ⦃ q ↦* values ⦄ (q.shift i).read
      ⦃ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read.spec (q.shift i) values[i] (hAlign.shift i)) <;> iframe

theorem read_unaligned.spec_range (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦* values ⦄ (q.shift i).read_unaligned
      ⦃ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read_unaligned.spec (q.shift i) values[i] (hNotNull.shift i)) <;> iframe

end RawPtr

theorem MutRawPtr.write_unaligned.spec_cells (q : MutRawPtr T)
    (cells : List (Option (Pointee.Cell T))) (value : T) (hLen : cells.length = Pointee.size T)
    (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦# cells ⦄ q.write_unaligned value ⦃ q ↦ value ⦄ := by
  unfold MutRawPtr.write_unaligned
  apply ispec_bind (Result.require.spec hNotNull)
  · iframe
  · intro _
    apply WP.ispec_mono (HeapOp.writes.spec q.loc cells (Pointee.toCells value)
      (by rw [Pointee.Lawful.length_toCells, hLen])) <;> iframe

@[step]
theorem MutRawPtr.write_unaligned.spec (q : MutRawPtr T) (oldValue newValue : T)
    (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦ oldValue ⦄ q.write_unaligned newValue ⦃ q ↦ newValue ⦄ :=
  write_unaligned.spec_cells q _ newValue (Pointee.Lawful.length_toCells oldValue) hNotNull

theorem MutRawPtr.write.spec_raw (q : MutRawPtr T) (cells : List (Option (Pointee.Cell T)))
    (value : T) (hLen : cells.length = Pointee.size T) (hAlign : q.Aligned) :
    ⦃ q ↦# cells ⦄ q.write value ⦃ q ↦ value ⦄ := by
  unfold MutRawPtr.write
  apply ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    apply WP.ispec_mono (write_unaligned.spec_cells q cells value hLen hAlign.notNull) <;> iframe

/-- Writing over a value or uninitialized memory. -/
theorem MutRawPtr.write.spec_opt (q : MutRawPtr T) (content : Option T) (value : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦? content ⦄ q.write value ⦃ q ↦ value ⦄ :=
  write.spec_raw q _ value (Pointee.length_optCells content) hAlign

@[step]
theorem MutRawPtr.write.spec (q : MutRawPtr T) (oldValue newValue : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃ q ↦ newValue ⦄ :=
  write.spec_raw q _ newValue (Pointee.Lawful.length_toCells oldValue) hAlign

theorem MutRawPtr.write.spec_range (q : MutRawPtr T) (values : List T)
    (i : Nat) (value : T) (hIndex : i < values.length)
    (hAlign : q.Aligned) :
    ⦃ q ↦* values ⦄ MutRawPtr.write (q.shift i) value
      ⦃ q ↦* values.set i value⦄ := by
  rw [RawPtr.pointsToRange_eq_take_get_drop hIndex,
    RawPtr.pointsToRange_eq_take_get_drop
      (show i < (values.set i value).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set,
    List.getElem_set_self]
  apply WP.ispec_mono (MutRawPtr.write.spec (q.shift i) values[i] value (hAlign.shift i)) <;>
    iframe

/-- `write.spec_range` on a range of values, some of which may be uninitialized. -/
theorem MutRawPtr.write.spec_cells (q : MutRawPtr T) (contents : List (Option T))
    (i : Nat) (value : T) (hIndex : i < contents.length)
    (hAlign : q.Aligned) :
    ⦃ q ↦*? contents ⦄ MutRawPtr.write (q.shift i) value
      ⦃ q ↦*? contents.set i (some value)⦄ := by
  rw [RawPtr.pointsToOpts_eq_take_get_drop hIndex,
    RawPtr.pointsToOpts_eq_take_get_drop
      (show i < (contents.set i (some value)).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set,
    List.getElem_set_self, RawPtr.pointsToOpt_some]
  apply WP.ispec_mono (MutRawPtr.write.spec_opt (q.shift i) contents[i] value (hAlign.shift i)) <;>
    iframe

theorem MutRawPtr.write.spec_head (q : MutRawPtr T) (values : List T) (value : T)
    (h : 0 < values.length) (hAlign : q.Aligned) :
    ⦃ q ↦* values ⦄ q.write value ⦃ q ↦* values.set 0 value⦄ := by
  simpa using MutRawPtr.write.spec_range q values 0 value h hAlign

namespace RawPtr

omit [Pointee.Lawful T] in
theorem borrow.spec_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) (value : T)
    (hLen : cells.length = Pointee.size T) (hValue : Pointee.ofCells cells = some value) :
    ⦃ q ↦# cells ⦄ q.borrow ⦃ result => ⌜result = value⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.borrow
  rw [pointsToBorrowed_one, ← hLen]
  apply ispec_bind (HeapOp.borrows.spec q.loc cells)
  · iframe
  · intro cs
    rw [sep_assoc_eq, ispec_ipure]
    rintro rfl
    apply WP.ispec_mono (Pointee.decode.spec hValue (P := emp)) <;> iframe

@[step]
theorem borrow.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.borrow ⦃ result => ⌜result = value⌝ ∗ q ↦† 1⦄ :=
  borrow.spec_cells q _ value (Pointee.Lawful.length_toCells value)
    (Pointee.Lawful.ofCells_toCells value)

@[step]
theorem endBorrow.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦† 1 ⦄ q.endBorrow value ⦃ q ↦ value⦄ := by
  unfold RawPtr.endBorrow
  rw [pointsToBorrowed_one, ← Pointee.Lawful.length_toCells value]
  exact HeapOp.endBorrows.spec q.loc _

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

/-- `endBorrowRange.spec` with the number of borrowed values given separately. -/
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
    apply WP.ispec_bind (load.spec q value)
    · iframe
    · intro v
      apply WP.ispec_bind (ih (q.shift 1))
      · iframe
      · intro vs
        apply (WP.ispec_ok _).2
        iframe

end RawPtr

@[step]
theorem core.ptr.from_mut.spec (value : T) :
    ⦃ emp ⦄ core.ptr.from_mut value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_mut q⌝ ∗ ⌜q.Aligned⌝ ∗ q ↦ value ∗
        q.freeable 1 .view⦄ := by
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
  apply WP.ispec_bind (RawPtr.load.spec q value)
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
theorem core.ptr.from_ref.spec (value : T) :
    ⦃ emp ⦄ core.ptr.from_ref value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_ref value q⌝ ∗ ⌜q.Aligned⌝ ∗ q ↦ value ∗
        q.freeable 1 .view⦄ := by
  unfold core.ptr.from_ref
  apply WP.ispec_bind (RawPtr.allocView.spec [value])
  · iframe
  · intro q
    apply (ispec_ok _).2
    simp only [uncurry_apply_pair, ← RawPtr.pointsTo_eq_range, List.length_singleton,
      RawPtr.pointsTo_cast_const, RawPtr.freeable_cast_const]
    iframe

@[step]
theorem core.ptr.end_from_ref.spec (q : ConstRawPtr T) (value : T) :
    ⦃ q ↦ value ∗ q.freeable 1 .view ⦄ core.ptr.end_from_ref value q ⦃ emp ⦄ := by
  unfold core.ptr.end_from_ref
  apply WP.ispec_bind (RawPtr.load.spec q value)
  · iframe
  · intro result
    rw [SepLogic.sep_assoc_eq, WP.ispec_ipure]
    rintro rfl
    apply WP.ispec_bind (RawPtr.endView.spec q [result] 1 rfl)
    · rw [← RawPtr.pointsTo_eq_range]
      iframe
    · intro _
      apply WP.ispec_mono (Result.require.spec rfl) <;> iframe

@[step]
theorem RawPtr.as_mut_unchecked.spec (q : MutRawPtr T) (value : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ value ⦄ q.as_mut_unchecked
      ⦃ (result, back) => ⌜result = value ∧ back = q.endBorrow⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.as_mut_unchecked
  apply WP.ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    apply WP.ispec_bind (RawPtr.borrow.spec q value)
    · iframe
    · intro v
      apply (ispec_ok _).2
      simp only [uncurry_apply_pair]
      iframe

@[step]
theorem RawPtr.as_ref_unchecked.spec (q : RawPtr T M) (value : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ value ⦄ q.as_ref_unchecked
      ⦃ (result, back) => ⌜result = value ∧ back = q.endBorrow value⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.as_ref_unchecked
  apply WP.ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    apply WP.ispec_bind (RawPtr.borrow.spec q value)
    · iframe
    · intro v
      apply (ispec_ok _).2
      simp only [uncurry_apply_pair]
      iframe

namespace RawPtr

theorem pointsTo_exclusive (q : RawPtr T M) (value₁ value₂ : T) (hSize : Pointee.size T ≠ 0) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ := by
  rintro h ⟨h₁, h₂, hCompatible, -, hP₁, hP₂⟩
  have hLen := fun v : T => Pointee.Lawful.length_toCells v
  exact Heap.not_compatible_of_isValid
    (HeapOp.isValid_of_array (i := 0) hP₁ (by rw [hLen]; omega))
    (HeapOp.isValid_of_array (i := 0) hP₂ (by rw [hLen]; omega)) hCompatible

theorem isValid_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) (hSize : Pointee.size T ≠ 0) :
    Heap.IsValid h q.cellPtr := by
  exact Heap.isValid_of_loc (HeapOp.isValid_of_array (i := 0) hPointsTo
    (by rw [Pointee.Lawful.length_toCells]; omega)) (by simp)

end RawPtr

omit [Pointee.Lawful T] in
theorem RawPtr.eq.spec_self (q : RawPtr T M) :
    ⦃ emp ⦄ q.eq q ⦃ b => ⌜b = true⌝⦄ := by
  rw [RawPtr.eq, ite_eq_left rfl]
  apply (ispec_ok _).2
  iframe

/-- Two different pointers into the same range of values are different. -/
theorem RawPtr.eq.spec_same_alloc (q : RawPtr T M) (values : List T) (i j : Nat)
    (hi : i ≤ values.length) (hj : j ≤ values.length) (hij : i ≠ j)
    (hNZ : Pointee.nonZero T) (hSize : Pointee.size T ≠ 0) :
    ⦃ q ↦* values ⦄ (q.shift i).eq (q.shift j) ⦃ b => ⌜b = false⌝ ∗ q ↦* values ⦄ := by
  have hOff : i * Pointee.size T ≠ j * Pointee.size T := fun h =>
    hij (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hSize) h)
  rw [RawPtr.eq, ite_eq_right fun h => hOff (by
    have := congrArg Loc.offset h
    simp only [RawPtr.loc_shift, Loc.offset_shift] at this
    omega)]
  apply ispec_guardedModify
  intro h hCells frame hCompatible
  have hLen := Pointee.length_flatMap_toCells (T := T) values
  have hLive := (q ↦* values).up_closed hCells (Heap.Subheap.union_left hCompatible)
  refine ⟨⟨hNZ, .inl ⟨by simp, ?_⟩⟩, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨rfl, hCells⟩⟩
  intro k hk
  have ha : i * Pointee.size T ≤ values.length * Pointee.size T := Nat.mul_le_mul_right _ hi
  have hb : j * Pointee.size T ≤ values.length * Pointee.size T := Nat.mul_le_mul_right _ hj
  simp only [RawPtr.loc_shift, Loc.offset_shift, Loc.allocId_shift] at hk ⊢
  clear hOff
  generalize i * Pointee.size T = a at *
  generalize j * Pointee.size T = b at *
  have hk' : min a b + k < (values.flatMap Pointee.toCells).length := by rw [hLen]; omega
  convert HeapOp.isValid_of_array hLive hk' using 2
  apply Loc.ext <;> simp; omega

/-- Two pointers to different live boxes are different. -/
theorem RawPtr.eq.spec_boxes (hNZ : Pointee.nonZero T) (hSize : Pointee.size T ≠ 0)
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
    refine ⟨hSize, RawPtr.isValid_of_pointsTo
      ((r ↦ u).up_closed (SepLogic.sep_elim_right _ _ h hR) hSub) hSize, ?_⟩
    have hEnd := ((RawPtr.freeable_holds r h).mp (SepLogic.sep_elim_left _ _ h hR)).2.trans hSub
    simpa using Heap.Subheap.isEndMarker hEnd
  exact ⟨⟨hNZ, .inr ⟨liveBox p v (by iframe), liveBox q w (by iframe)⟩⟩, h, hCompatible, rfl,
    pure_sep_intro _ rfl h hPre⟩

omit [Pointee.Lawful T] in
/-- Comparing a pointer to a borrow view (see `core.ptr.from_mut.spec`) with a pointer into
another allocation fails. -/
theorem RawPtr.eq.fails_view {p q : RawPtr T M}
    (hBase : p.loc.allocId ≠ q.loc.allocId) :
    ifails (p.freeable 1 .view) (p.eq q) := by
  rw [RawPtr.eq, ite_eq_right fun h => hBase (congrArg Loc.allocId h)]
  apply ifails_guardedModify
  intro h hFreeable h' hSub hPre
  rcases hPre.2 with hEq | ⟨⟨_, _, hBox⟩, _⟩
  · exact hBase hEq.1
  · have hView := Heap.Subheap.isEndMarker (hFreeable.2.trans hSub)
    rw [Nat.one_mul] at hView
    exact absurd (Heap.isEndMarker_unique hView hBox) (by decide)

/-- Comparing two pointers to different cells of a type which may be zero-sized fails. -/
theorem RawPtr.eq.fails_zero_sized (hZ : Pointee.nonZero T = false) (hSize : Pointee.size T ≠ 0)
    {p q : RawPtr T M} (v w : T) : ifails (p ↦ v ∗ q ↦ w) (p.eq q) := by
  by_cases hA : p.loc = q.loc
  · refine ifails_mono (P' := ⌜False⌝ ∗ emp) ?_ (ifails_ipure False.elim)
    rw [sep_emp_r_eq, RawPtr.ext hA]
    exact RawPtr.pointsTo_exclusive q v w hSize
  · rw [RawPtr.eq, ite_eq_right hA]
    apply ifails_guardedModify
    intro _ _ _ _ hPre
    exact absurd hPre.1 (by simp [hZ])

namespace RawPtr

omit [Pointee.Lawful T] in
/-- `add` stays in bounds of the cells `q` owns. -/
theorem add.spec_raw (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (count : Usize) (hCount : count.val * Pointee.size T ≤ cells.length) :
    ⦃ q ↦# cells ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦# cells⦄ := by
  apply ispec_guardedModify
  intro h hCells frame hCompatible
  refine ⟨HeapOp.live_of_array ((q ↦# cells).up_closed hCells (Heap.Subheap.union_left hCompatible))
    hCount, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨rfl, hCells⟩⟩

@[step]
theorem add.spec (q : RawPtr T M) (values : List T) (count : Usize)
    (hCount : count.val ≤ values.length) :
    ⦃ q ↦* values ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦* values⦄ :=
  add.spec_raw q _ count
    (by rw [Pointee.length_flatMap_toCells]; exact Nat.mul_le_mul_right _ hCount)

/-- `add` on a range of values, some of which may be uninitialized. -/
theorem add.spec_cells (q : RawPtr T M) (contents : List (Option T)) (count : Usize)
    (hCount : count.val ≤ contents.length) :
    ⦃ q ↦*? contents ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦*? contents⦄ :=
  add.spec_raw q _ count
    (by rw [Pointee.length_flatMap_optCells]; exact Nat.mul_le_mul_right _ hCount)

omit [Pointee.Lawful T] in
/-- `offset` from the `k`-th cell of a range of cells, staying in the range. -/
theorem offset.spec_raw (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) (k : Nat)
    (count : Isize) (hk : k ≤ cells.length)
    (hTarget : 0 ≤ (k : Int) + count.val * Pointee.size T)
    (hEnd : (k : Int) + count.val * Pointee.size T ≤ cells.length) :
    ⦃ q ↦# cells ⦄ (q.shiftCells k).offsetBy count
      ⦃ result => ⌜result = q.shiftCells ((k : Int) + count.val * Pointee.size T).toNat⌝ ∗
        q ↦# cells⦄ := by
  apply ispec_guardedModify
  intro h hCells frame hCompatible
  have hLive := (q ↦# cells).up_closed hCells (Heap.Subheap.union_left hCompatible)
  refine ⟨⟨by simp only [loc_shiftCells, Loc.offset_shift]; omega, ?_⟩, h, hCompatible, rfl,
    (sep_pure_l _ _ h).mpr ⟨?_, hCells⟩⟩
  · intro i hi
    simp only [loc_shiftCells, Loc.offset_shift, Loc.allocId_shift] at hi ⊢
    have hc := HeapOp.isValid_of_array (i := min (q.loc.offset + k)
      (((q.loc.offset + k : Nat) : Int) + count.val * Pointee.size T).toNat - q.loc.offset + i)
      hLive (by omega)
    convert hc using 2
    apply Loc.ext <;> simp; omega
  · apply RawPtr.ext
    apply Loc.ext <;> simp; omega

/-- `offset` on a range of values, staying in the range. -/
theorem offset.spec (q : RawPtr T M) (values : List T) (i : Nat) (count : Isize)
    (hi : i ≤ values.length) (hTarget : 0 ≤ (i : Int) + count.val)
    (hEnd : (i : Int) + count.val ≤ values.length) :
    ⦃ q ↦* values ⦄ (q.shift i).offsetBy count
      ⦃ result => ⌜result = q.shift ((i : Int) + count.val).toNat⌝ ∗ q ↦* values⦄ := by
  have hLen := Pointee.length_flatMap_toCells (T := T) values
  have hPtr : q.shiftCells (((i * Pointee.size T : Nat) : Int) + count.val * Pointee.size T).toNat =
      q.shift ((i : Int) + count.val).toNat := by
    rw [shift_eq_shiftCells]
    congr 1
    have : ((i * Pointee.size T : Nat) : Int) + count.val * Pointee.size T =
        (((i : Int) + count.val).toNat * Pointee.size T : Nat) := by
      push_cast; rw [Int.toNat_of_nonneg hTarget, Int.add_mul]
    rw [this, Int.toNat_natCast]
  have hSpec := offset.spec_raw q _ (i * Pointee.size T) count
    (by rw [hLen]; exact Nat.mul_le_mul_right _ hi)
    (by push_cast; rw [← Int.add_mul]; exact Int.mul_nonneg hTarget (Int.natCast_nonneg _))
    (by
      rw [hLen]; push_cast; rw [← Int.add_mul]
      exact Int.mul_le_mul_of_nonneg_right hEnd (Int.natCast_nonneg _))
  rw [hPtr] at hSpec
  exact hSpec

/-- The distance between two pointers into a range of values. -/
theorem offset_from.spec (q : RawPtr T M) (values : List T) (i j : Nat)
    (hi : i ≤ values.length) (hj : j ≤ values.length) (hNZ : Pointee.nonZero T)
    (hSize : Pointee.size T ≠ 0)
    (hBound : -2 ^ (IScalarTy.Isize.numBits - 1) ≤ (i : Int) - j ∧
      (i : Int) - j < 2 ^ (IScalarTy.Isize.numBits - 1)) :
    ⦃ q ↦* values ⦄ (q.shift i).offset_from (⟨(q.shift j).loc⟩ : RawPtr T M')
      ⦃ result => ⌜result.val = (i : Int) - j⌝ ∗ q ↦* values⦄ := by
  have hLen := Pointee.length_flatMap_toCells (T := T) values
  have hDist : (((q.shift i).loc.offset : Int) - (q.shift j).loc.offset) =
      ((i : Int) - j) * Pointee.size T := by
    simp only [loc_shift, Loc.offset_shift]; push_cast; rw [Int.sub_mul]; omega
  have hDiv : ((((q.shift i).loc.offset : Int) - (q.shift j).loc.offset) /
      Pointee.size T) = (i : Int) - j := by
    rw [hDist, Int.mul_ediv_cancel _ (by exact_mod_cast hSize)]
  unfold RawPtr.offset_from
  apply ispec_guardedModify
  intro h hCells frame hCompatible
  have hLive := (q ↦* values).up_closed hCells (Heap.Subheap.union_left hCompatible)
  refine ⟨⟨by simp, hNZ, hSize, ⟨(i : Int) - j, by rw [hDist, Int.mul_comm]⟩, ?_,
    by rw [hDiv]; exact hBound.1, by rw [hDiv]; exact hBound.2⟩, h, hCompatible, rfl,
    (sep_pure_l _ _ h).mpr ⟨?_, hCells⟩⟩
  · intro k hk
    have ha : i * Pointee.size T ≤ values.length * Pointee.size T := Nat.mul_le_mul_right _ hi
    have hb : j * Pointee.size T ≤ values.length * Pointee.size T := Nat.mul_le_mul_right _ hj
    simp only [loc_shift, Loc.offset_shift, Loc.allocId_shift] at hk ⊢
    clear hDist hDiv
    generalize i * Pointee.size T = a at *
    generalize j * Pointee.size T = b at *
    have hk' : min a b + k < (values.flatMap Pointee.toCells).length := by rw [hLen]; omega
    convert HeapOp.isValid_of_array hLive hk' using 2
    apply Loc.ext <;> simp; omega
  · simp only [IScalar.ofInt_val_eq]
    exact hDiv

end RawPtr

/-! #### Copies -/

omit [Pointee.Lawful T] in
/-- Copy between two separate ranges of cells. -/
theorem core.ptr.copy.spec_raw (src : ConstRawPtr T) (dst : MutRawPtr T)
    (srcCells dstCells : List (Option (Pointee.Cell T))) (count : Usize)
    (hSrc : srcCells.length = count.val * Pointee.size T)
    (hDst : dstCells.length = count.val * Pointee.size T)
    (hAlign : src.Aligned ∧ dst.Aligned ∧ src.NotNull (count.val * Pointee.size T) ∧
      dst.NotNull (count.val * Pointee.size T)) :
    ⦃ src ↦# srcCells ∗ dst ↦# dstCells ⦄ core.ptr.copy src dst count
      ⦃ src ↦# srcCells ∗ dst ↦# srcCells ⦄ := by
  unfold core.ptr.copy
  apply WP.ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    rw [← hSrc]
    apply WP.ispec_bind (HeapOp.reads.spec src.loc srcCells)
    · iframe
    · intro cs
      rw [sep_assoc_eq, ispec_ipure]
      rintro rfl
      apply WP.ispec_mono (HeapOp.writes.spec dst.loc dstCells cs (by rw [hSrc, hDst]))
      · iframe
      · iframe

@[step]
theorem core.ptr.copy.spec (src : ConstRawPtr T) (dst : MutRawPtr T)
    (srcValues dstValues : List T)
    (count : Usize) (hSrc : srcValues.length = count.val) (hDst : dstValues.length = count.val)
    (hAlignSrc : src.Aligned) (hAlignDst : dst.Aligned)
    (hNotNullSrc : src.NotNull (count.val * Pointee.size T))
    (hNotNullDst : dst.NotNull (count.val * Pointee.size T)) :
    ⦃ src ↦* srcValues ∗ dst ↦* dstValues ⦄ core.ptr.copy src dst count
      ⦃ src ↦* srcValues ∗ dst ↦* srcValues ⦄ :=
  core.ptr.copy.spec_raw src dst _ _ count
    (by rw [Pointee.length_flatMap_toCells, hSrc]) (by rw [Pointee.length_flatMap_toCells, hDst])
    ⟨hAlignSrc, hAlignDst, hNotNullSrc, hNotNullDst⟩

omit [Pointee.Lawful T] in
/-- Two ranges of cells owned separately do not overlap. -/
theorem RawPtr.disjoint_of_sep {src : ConstRawPtr T} {dst : MutRawPtr T}
    {srcCells dstCells : List (Option (Pointee.Cell T))} {h : Heap}
    (hSep : (src ↦# srcCells ∗ dst ↦# dstCells) h) (n : Nat)
    (hSrc : n ≤ srcCells.length) (hDst : n ≤ dstCells.length) :
    src.loc.allocId ≠ dst.loc.allocId ∨ src.loc.offset + n ≤ dst.loc.offset ∨
      dst.loc.offset + n ≤ src.loc.offset := by
  by_contra hOverlap
  simp only [not_or, not_not, Nat.not_le] at hOverlap
  obtain ⟨hBase, h₁, h₂⟩ := hOverlap
  obtain ⟨hs, hd, hCompatible, -, hS, hD⟩ := hSep
  by_cases hle : src.loc.offset ≤ dst.loc.offset
  · have hcs := HeapOp.isValid_of_array (i := dst.loc.offset - src.loc.offset) hS (by omega)
    have hcd := HeapOp.isValid_of_array (i := 0) hD (by omega)
    refine Heap.not_compatible_of_isValid hcs ?_ hCompatible
    convert hcd using 2
    apply Loc.ext <;> simp [hBase]; omega
  · have hcs := HeapOp.isValid_of_array (i := 0) hS (by omega)
    have hcd := HeapOp.isValid_of_array (i := src.loc.offset - dst.loc.offset) hD (by omega)
    refine Heap.not_compatible_of_isValid hcs ?_ hCompatible
    convert hcd using 2
    apply Loc.ext <;> simp [hBase]; omega

omit [Pointee.Lawful T] in
theorem core.ptr.copy_nonoverlapping.spec_raw (src : ConstRawPtr T) (dst : MutRawPtr T)
    (srcCells dstCells : List (Option (Pointee.Cell T))) (count : Usize)
    (hSrc : srcCells.length = count.val * Pointee.size T)
    (hDst : dstCells.length = count.val * Pointee.size T)
    (hAlign : src.Aligned ∧ dst.Aligned ∧ src.NotNull (count.val * Pointee.size T) ∧
      dst.NotNull (count.val * Pointee.size T)) :
    ⦃ src ↦# srcCells ∗ dst ↦# dstCells ⦄ core.ptr.copy_nonoverlapping src dst count
      ⦃ src ↦# srcCells ∗ dst ↦# srcCells ⦄ := by
  unfold core.ptr.copy_nonoverlapping
  apply WP.ispec_bind (Pm := iprop(src ↦# srcCells ∗ dst ↦# dstCells)) (F := emp)
    (Qm := fun _ => iprop(src ↦# srcCells ∗ dst ↦# dstCells))
  · apply ispec_guardedModify
    intro h hSep frame hCompatible
    exact ⟨RawPtr.disjoint_of_sep hSep _ (by omega) (by omega), h, hCompatible, rfl, hSep⟩
  · iframe
  · intro _
    apply WP.ispec_mono (core.ptr.copy.spec_raw src dst srcCells dstCells count hSrc hDst hAlign)
      <;> iframe

@[step]
theorem core.ptr.copy_nonoverlapping.spec (src : ConstRawPtr T) (dst : MutRawPtr T)
    (srcValues dstValues : List T) (count : Usize) (hSrc : srcValues.length = count.val)
    (hDst : dstValues.length = count.val)
    (hAlignSrc : src.Aligned) (hAlignDst : dst.Aligned)
    (hNotNullSrc : src.NotNull (count.val * Pointee.size T))
    (hNotNullDst : dst.NotNull (count.val * Pointee.size T)) :
    ⦃ src ↦* srcValues ∗ dst ↦* dstValues ⦄ core.ptr.copy_nonoverlapping src dst count
      ⦃ src ↦* srcValues ∗ dst ↦* srcValues ⦄ :=
  core.ptr.copy_nonoverlapping.spec_raw src dst _ _ count
    (by rw [Pointee.length_flatMap_toCells, hSrc]) (by rw [Pointee.length_flatMap_toCells, hDst])
    ⟨hAlignSrc, hAlignDst, hNotNullSrc, hNotNullDst⟩

omit [Pointee.Lawful T] in
/-- `write_bytes` on byte cells. -/
theorem core.ptr.write_bytes.spec (dst : MutRawPtr T) (cells : List (Option U8)) (value : U8)
    (count : Usize) (hLen : cells.length = count.val * Pointee.size T)
    (hByte : Pointee.Cell T = U8) (hAlign : dst.Aligned)
    (hNotNull : dst.NotNull (count.val * Pointee.size T)) :
    ⦃ owns (Heap.array dst.loc cells) ⦄ core.ptr.write_bytes dst value count
      ⦃ owns (Heap.array dst.loc (List.replicate (count.val * Pointee.size T) (some value))) ⦄ := by
  unfold core.ptr.write_bytes
  apply WP.ispec_bind (Result.require.spec ⟨hByte, hAlign, hNotNull⟩)
  · iframe
  · intro _
    apply WP.ispec_mono (HeapOp.writes.spec dst.loc cells _ (by simp [hLen])) <;> iframe

/-- A transmute decodes the cells of the value at the target type. -/
theorem core.mem.transmute.spec {A B : Type} [Pointee A] [Pointee B] (x : A)
    (hCell : Pointee.Cell A = Pointee.Cell B) (hSize : Pointee.size A = Pointee.size B)
    (value : B)
    (hValue : Pointee.ofCells (cast (congrArg (fun α => List (Option α)) hCell)
      (Pointee.toCells x)) = some value) :
    ⦃ emp ⦄ core.mem.transmute B x ⦃ r => ⌜r = value⌝ ⦄ := by
  unfold core.mem.transmute
  apply WP.ispec_bind (Pm := emp) (F := emp)
    (Qm := fun cs => ⌜cs = cast (congrArg (fun α => List (Option α)) hCell) (Pointee.toCells x)⌝)
  · apply ispec_guardedModify
    intro h _ frame hCompatible
    exact ⟨⟨hCell, hSize⟩, h, hCompatible, rfl, rfl⟩
  · iframe
  · intro cs
    rw [ispec_ipure]
    rintro rfl
    apply WP.ispec_mono (Pointee.decode.spec hValue (P := emp)) <;> iframe

@[step]
theorem core.ptr.drop_in_place.spec (p : MutRawPtr T) (value : T)
    (hAlign : p.Aligned) :
    ⦃ p ↦ value ⦄ core.ptr.drop_in_place p ⦃ p ↦? none ⦄ := by
  unfold core.ptr.drop_in_place
  apply WP.ispec_bind (RawPtr.read.spec p value hAlign)
  · iframe
  · intro _
    apply WP.ispec_mono (HeapOp.writes.spec p.loc (Pointee.toCells value) _
      (by rw [Pointee.length_optCells, Pointee.Lawful.length_toCells])) <;> iframe

end Specs

/-! ### Undefined behaviours rejected by the model -/

section Fails

variable {T : Type} [Pointee T] {M : Mutability}

namespace RawPtr

theorem read.fails_misaligned (q : RawPtr T M) (hNot : ¬ q.Aligned) {P : IPre} :
    ifails P q.read :=
  ifails_bind_left (Result.require.fails hNot)

theorem write.fails_misaligned (q : MutRawPtr T) (value : T) (hNot : ¬ q.Aligned) {P : IPre} :
    ifails P (MutRawPtr.write q value) :=
  ifails_bind_left (Result.require.fails hNot)

/-- Accessing a zero-sized value through the null pointer fails (when some cells are accessed,
the access fails since the allocation `0` is never allocated). -/
theorem read_unaligned.fails_null (q : RawPtr T M) (hNull : q.loc.allocId = 0)
    (hSize : Pointee.size T = 0) {P : IPre} : ifails P q.read_unaligned :=
  ifails_bind_left (Result.require.fails (by simp [hNull, hSize]))

theorem write_unaligned.fails_null (q : MutRawPtr T) (value : T) (hNull : q.loc.allocId = 0)
    (hSize : Pointee.size T = 0) {P : IPre} : ifails P (MutRawPtr.write_unaligned q value) :=
  ifails_bind_left (Result.require.fails (by simp [hNull, hSize]))

/-- Pointer arithmetic over cells which are not cells of the pointee fails: it would count cells
of another size (e.g. bytes for a pointer to a typed value). -/
theorem add.fails_cells {α : Type} (q : RawPtr T M) (cells : List (Option α)) (count : Usize)
    (hNe : α ≠ Pointee.Cell T) (hLen : 0 < cells.length)
    (hCount : 0 < count.val * Pointee.size T) :
    ifails (owns (Heap.array q.loc cells)) (q.add count) := by
  apply ifails_guardedModify
  intro h hCells h' hSub hPre
  exact hNe (Heap.isValid_unique
    (HeapOp.isValid_of_array (i := 0) (IProp.up_closed _ hCells hSub) hLen) (hPre 0 hCount) rfl)

/-- `offset_from` over cells which are not cells of the pointee fails. -/
theorem offset_from.fails_cells {α : Type} (p : RawPtr T M) (origin : RawPtr T M')
    (cells : List (Option α)) (hNe : α ≠ Pointee.Cell T) (hLen : 0 < cells.length)
    (hDist : p.loc.offset ≠ origin.loc.offset) :
    ifails (owns (Heap.array ⟨p.loc.allocId, min p.loc.offset origin.loc.offset⟩ cells))
      (p.offset_from origin) := by
  apply ifails_guardedModify
  intro h hCells h' hSub hPre
  exact hNe (Heap.isValid_unique
    (HeapOp.isValid_of_array (i := 0) (IProp.up_closed _ hCells hSub) hLen)
    (hPre.2.2.2.2.1 0 (by omega)) rfl)

/-- `write_bytes` fails unless the cells of the pointee are bytes, and the pointer is aligned (and
not null, even if no byte is written). -/
theorem _root_.Aeneas.Std.core.ptr.write_bytes.fails (dst : MutRawPtr T) (value : U8)
    (count : Usize)
    (hNot : ¬ (Pointee.Cell T = U8 ∧ dst.Aligned ∧ dst.NotNull (count.val * Pointee.size T)))
    {P : IPre} :
    ifails P (core.ptr.write_bytes dst value count) :=
  ifails_bind_left (Result.require.fails hNot)

/-- Reading cells which hold no value of the pointee (uninitialized cells, invalid bytes...)
fails. -/
theorem load.fails_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (hLen : cells.length = Pointee.size T) (hNone : Pointee.ofCells cells = none) :
    ifails (q ↦# cells) q.load := by
  unfold RawPtr.load
  rw [← hLen]
  exact ifails_bind (HeapOp.reads.spec q.loc cells) fun cs =>
    ifails_ipure fun h => by subst h; exact Pointee.decode.fails hNone

theorem read_unaligned.fails_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (hLen : cells.length = Pointee.size T) (hNone : Pointee.ofCells cells = none) :
    ifails (q ↦# cells) q.read_unaligned := by
  unfold RawPtr.read_unaligned
  exact ifails_require_bind (load.fails_cells q cells hLen hNone)

theorem read.fails_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (hLen : cells.length = Pointee.size T) (hNone : Pointee.ofCells cells = none) :
    ifails (q ↦# cells) q.read :=
  ifails_require_bind (read_unaligned.fails_cells q cells hLen hNone)

/-- Reading uninitialized memory fails. -/
theorem read.fails_uninit [Pointee.UninitInvalid T] (q : RawPtr T M) :
    ifails (q ↦? none) q.read :=
  read.fails_cells q _ (by simp) Pointee.UninitInvalid.ofCells_uninit

/-- Decoding `size T > 0` cells starting with a slot which is owned and holds no value fails. -/
private theorem load.fails_of_reads {q : RawPtr T M} {A : IProp} (hSize : Pointee.size T ≠ 0)
    (hReads : ∀ n, 0 < n → ifails A (HeapOp.reads (Pointee.Cell T) q.loc n)) :
    ifails A q.load := by
  unfold RawPtr.load
  exact ifails_bind_left (hReads _ (by omega))

theorem load.fails_borrowed (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) :
    ifails (q ↦† 1) q.load := by
  obtain ⟨n, hn⟩ : ∃ n, Pointee.size T = n + 1 := ⟨Pointee.size T - 1, by omega⟩
  rw [pointsToBorrowed_one, hn, HeapOp.borrowedAt_succ]
  exact load.fails_of_reads hSize fun m hm =>
    ifails_mono (sep_elim_right _ _) (HeapOp.reads.fails_borrowed _ _ _ hm)

/-- Reading a borrowed value (moved out by `from_raw_parts` or a borrow) fails. -/
theorem read.fails_borrowed (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) :
    ifails (q ↦† 1) q.read :=
  ifails_require_bind (ifails_require_bind (load.fails_borrowed q hSize))

theorem load.fails_freed (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) :
    ifails q.freed q.load :=
  load.fails_of_reads hSize fun _ hm => HeapOp.reads.fails_freed _ _ _ hm

/-- Reading freed memory fails. -/
theorem read.fails_freed (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) :
    ifails q.freed q.read :=
  ifails_require_bind (ifails_require_bind (load.fails_freed q hSize))

theorem load.fails_end (q : RawPtr T M) (count : Nat) (kind : AllocKind)
    (hSize : Pointee.size T ≠ 0) : ifails (q.freeable count kind) (q.shift count).load := by
  refine load.fails_of_reads hSize fun n hn => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [HeapOp.reads]
  apply ifails_bind_left
  apply ifails_guardedModify
  intro h hFreeable h' hSub hValid
  exact Heap.not_isLive_of_isEndMarker (Heap.Subheap.isEndMarker (hFreeable.2.trans hSub))
    (by simpa using Heap.isLive_of_isValid hValid)

/-- Reading the end marker of an allocation (one past its last value) fails. -/
theorem read.fails_end (q : RawPtr T M) (count : Nat) (kind : AllocKind)
    (hSize : Pointee.size T ≠ 0) : ifails (q.freeable count kind) (q.shift count).read :=
  ifails_require_bind (ifails_require_bind (load.fails_end q count kind hSize))

/-- Moving a value out of a borrowed slot fails. -/
theorem borrow.fails_borrowed (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) :
    ifails (q ↦† 1) q.borrow := by
  obtain ⟨n, hn⟩ : ∃ n, Pointee.size T = n + 1 := ⟨Pointee.size T - 1, by omega⟩
  rw [pointsToBorrowed_one, hn, HeapOp.borrowedAt_succ]
  unfold RawPtr.borrow
  rw [hn]
  exact ifails_bind_left (ifails_mono (sep_elim_right _ _)
    (HeapOp.borrows.fails_borrowed _ _ (n + 1) (by omega)))

/-- `&mut *q` while `*q` is borrowed fails. -/
theorem as_mut_unchecked.fails_borrowed (q : MutRawPtr T) (hSize : Pointee.size T ≠ 0) :
    ifails (q ↦† 1) q.as_mut_unchecked :=
  ifails_require_bind (ifails_bind_left (borrow.fails_borrowed q hSize))

/-- `&*q` while `*q` is borrowed fails. -/
theorem as_ref_unchecked.fails_borrowed (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) :
    ifails (q ↦† 1) q.as_ref_unchecked :=
  ifails_require_bind (ifails_bind_left (borrow.fails_borrowed q hSize))

/-- Moving out of cells which hold no value of the pointee fails. -/
theorem borrow.fails_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (hLen : cells.length = Pointee.size T) (hNone : Pointee.ofCells cells = none) :
    ifails (q ↦# cells) q.borrow := by
  unfold RawPtr.borrow
  rw [← hLen]
  exact ifails_bind (HeapOp.borrows.spec q.loc cells) fun cs =>
    ifails_ipure fun h => by subst h; exact Pointee.decode.fails hNone

/-- Borrowing a range which contains cells holding no value of the pointee (for instance,
uninitialized cells) fails. -/
theorem borrowRange.fails [Pointee.Lawful T] (q : RawPtr T M) (values : List T)
    (cells : List (Option (Pointee.Cell T))) (hLen : cells.length = Pointee.size T)
    (hNone : Pointee.ofCells cells = none) (n : Nat) (hn : values.length < n) :
    ifails iprop(q ↦* values ∗ (q.shift values.length) ↦# cells) (q.borrowRange n) := by
  induction values generalizing q n with
  | nil =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [borrowRange]
    apply ifails_bind_left
    refine ifails_mono ?_ (borrow.fails_cells q cells hLen hNone)
    simp only [pointsToRange_nil, List.length_nil, shift_zero]
    iframe
  | cons value values ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [borrowRange]
    have hF := ispec_frame (borrow.spec q value)
      iprop((q.shift 1) ↦* values ∗ ((q.shift 1).shift values.length) ↦# cells)
    refine ifails_mono ?_ (ifails_bind hF fun x => ifails_bind_left
      (ifails_mono ?_ (ih (q.shift 1) m (by simp at hn; omega))))
    · rw [pointsToRange_cons, List.length_cons, shift_shift, Nat.add_comm]
      iframe
    · exact SepLogic.sep_elim_left _ _

end RawPtr

end Fails

end Aeneas.Std
