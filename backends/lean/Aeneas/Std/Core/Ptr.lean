/- `core::ptr` -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Heap
public import Aeneas.Std.Scalar.Core
@[expose] public section

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

/-- Not a Rust function: moves the value out into a borrow; the slot stays `borrowed` until
`endBorrow`. -/
def RawPtr.take (q : RawPtr T M) : Result T :=
  Result.guardedModify _ (Heap.borrow q)

/-- Not a Rust function: ends the borrow of the slot of `q`, which holds `value` again. -/
def RawPtr.endBorrow (q : RawPtr T M) (value : T) : Result Unit :=
  Result.guardedModify _ (Heap.endBorrow q value)

/-- Not a Rust function: `take` on the `n` slots from `q` on. -/
def RawPtr.takeRange (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.take
    let values ← (q.shift 1).takeRange n
    .ok (value :: values)

/-- Not a Rust function: `endBorrow` on the `values.length` slots from `q` on. -/
def RawPtr.endBorrowRange (q : RawPtr T M) : List T → Result Unit
  | [] => .ok ()
  | value :: values => do
    q.endBorrow value
    (q.shift 1).endBorrowRange values

/-- Not a Rust function: `read` on the `n` slots from `q` on. -/
def RawPtr.readRange (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.read
    let values ← (q.shift 1).readRange n
    .ok (value :: values)

/-- Not a Rust function: a raw-pointer view of a place owned elsewhere (`from_mut`, `as_ptr`,
`as_mut_ptr`). The functional model gives the place no address, so the view is a fresh allocation
holding a copy of `values`, which only `endView` frees (`AllocKind.view`). -/
def RawPtr.allocView (values : List T) : Result (MutRawPtr T) :=
  Result.guardedModify (fun _ => True) fun h _ => h.alloc values .view

/-- Not a Rust function: ends the view behind `q`, which holds `count` values: the whole allocation
is freed, so every later use of a pointer into it fails. -/
def RawPtr.endView (q : RawPtr T M) (count : Nat) : Result Unit :=
  Result.guardedModify _ (Heap.dealloc q.loc count .view)

/-- Not a Rust function: fails unless `p` holds (`p` need not be decidable). -/
def Result.require (p : Prop) : Result Unit :=
  Result.guardedModify (fun _ => p) fun h _ => ((), h)

/-- Not a Rust function: end of the borrow given to `from_mut`; reads the value, with the writes
made through the pointer, and ends the view, so that the pointer can't be used anymore. -/
def core.ptr.end_from_mut (p : MutRawPtr T) : Result T := do
  let value ← p.read
  p.endView 1
  .ok value

/-- The pointer is a view of `r`; the back computation runs when the borrow ends. -/
def core.ptr.from_mut (r : T) : Result (MutRawPtr T × Result T) :=
  Aeneas.Std.bind (RawPtr.allocView [r]) fun p => .ok (p, core.ptr.end_from_mut p)

end Aeneas.Std
