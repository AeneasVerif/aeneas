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

@[expose, reducible, rust_type "core::ptr::alignment::Alignment"]
def core.ptr.alignment.Alignment :=
core.ptr.alignment.AlignmentEnum

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp

/-! `core::ptr`: the raw-pointer methods (from `core::ptr::mut_ptr` and `core::ptr::const_ptr`) and
the module functions. Each definition with a `rust_fun` pattern models that Rust function, with the
signature Aeneas gives it: a `&mut T` argument is returned updated next to the result. The others
are not Rust functions: `InBounds` is the precondition of `add`; `materialize` stores values in a
fresh allocation (behind `from_mut`, `Slice::as_ptr`/`as_mut_ptr`, and the global allocator in
`Alloc/Alloc.lean`); and `cast_scalar` is the `as` cast between scalar raw pointers that the
extractor emits by name. -/

/-- A fresh allocation holding `values`. If `freeable`, it comes from the global allocator and only
`Global.deallocate` frees it; otherwise it is a local, behind a pointer from `from_mut` or
`as_mut_ptr`. -/
def RawPtr.materialize (values : List T) (freeable : Bool := false) : Result (RawPtr T M) :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (⟨Heap.freshLoc h⟩, Heap.alloc h values freeable)

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
  Result.guardedModify (fun h => Heap.IsValid h q) fun h hValid =>
    (h.read q hValid, h)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read"] read
attribute [rust_fun "core::ptr::read"] read

end RawPtr

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write"]
def MutRawPtr.write (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.guardedModify (fun h => Heap.IsValid h q) fun h hValid =>
    ((), h.write q value hValid)

attribute [rust_fun "core::ptr::write"] MutRawPtr.write

/-- Not a Rust function: moves the value out and frees its slot. -/
def RawPtr.take (q : RawPtr T M) : Result T :=
  Result.guardedModify (fun h => Heap.IsValid h q) fun h hValid =>
    (h.read q hValid, h.free q hValid)

/-- Not a Rust function: brings the freed slot of `q` back to life, holding `value`. -/
def RawPtr.revive (q : RawPtr T M) (value : T) : Result Unit :=
  Result.guardedModify (fun h => Heap.IsFreed h q.loc) fun h hFreed =>
    ((), h.revive q value hFreed)

/-- Not a Rust function: `take` on the `n` slots from `q` on. -/
def RawPtr.takeRange (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.take
    let values ← (q.shift 1).takeRange n
    .ok (value :: values)

/-- Not a Rust function: `revive` on the `values.length` slots from `q` on. -/
def RawPtr.reviveRange (q : RawPtr T M) : List T → Result Unit
  | [] => .ok ()
  | value :: values => do
    q.revive value
    (q.shift 1).reviveRange values

/-- Not a Rust function: fails unless `p` holds (`p` need not be decidable). -/
def Result.require (p : Prop) : Result Unit :=
  Result.guardedModify (fun _ => p) fun h _ => ((), h)

/-- Not a Rust function: end of the borrow given to `from_mut`; moves the value, with the writes
made through the pointer, out of the slot and frees it, so that the pointer can't be used anymore. -/
def core.ptr.end_from_mut (p : MutRawPtr T) : Result T :=
  p.take

/-- The pointer points to a fresh slot holding `r`; the back computation runs when the borrow
ends (`statefulLifetimes`). -/
@[rust_fun "core::ptr::from_mut" (statefulLifetimes := [0])]
def core.ptr.from_mut (r : T) : Result (MutRawPtr T × Result T) :=
  Aeneas.Std.bind (RawPtr.materialize [r]) fun p => .ok (p, core.ptr.end_from_mut p)

end Aeneas.Std
