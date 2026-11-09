/- `core::ptr` -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Heap
public import Aeneas.Std.Core.Pointee
public import Aeneas.Std.Scalar.Core
public section

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

/-- Compatibility argument of the existing, unsupported scalar-pointer cast wrapper only. -/
inductive Mutability where
  | Mut
  | Const

/-- Always fails: scalar pointer casts are not modelled by the current wrapper API. -/
def RawPtr.cast_scalar {T} (T' : Type) (_ : Mutability) [IsScalar T] [IsScalar T']
    (_ : RawPtr T) : Result (RawPtr T') :=
  .fail .undef

/- Thin raw-pointer casts/transmutes preserve allocation identity and byte offset.
No representation, alignment, or bounds check is needed to form the pointer. In particular,
misaligned pointers are representable; typed accesses check alignment, bounds, permissions,
and decoding. Casting changes neither bytes nor permissions and assumes no decoder relation.
This helper is used by manually adapted examples, not yet inserted by the compiler. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::add"]
def RawPtr.add [Pointee T] (q : RawPtr T) (count : Usize) : Result (RawPtr T) :=
  Result.checkedModify (State.offset (Pointee.repr (T := T)) q count.val)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::add"] RawPtr.add

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::offset"]
def RawPtr.offset [Pointee T] (q : RawPtr T) (count : Isize) : Result (RawPtr T) :=
  Result.checkedModify (State.offset (Pointee.repr (T := T)) q count.val)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::offset"] RawPtr.offset

@[expose, rust_fun "core::ptr::mut_ptr::{*mut @T}::cast_const" -canFail -lift]
def RawPtr.cast_const (q : MutRawPtr T) : ConstRawPtr T :=
  q

@[simp] theorem RawPtr.cast_const_eq (q : MutRawPtr T) : q.cast_const = q := rfl

namespace RawPtr

@[rust_fun "core::ptr::const_ptr::{*const @T}::read"]
def read [Pointee T] (q : RawPtr T) : Result T :=
  Result.checkedModify (State.read (Pointee.repr (T := T)) q)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read"] read
attribute [rust_fun "core::ptr::read"] read

end RawPtr

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write"]
def MutRawPtr.write [Pointee T] (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.checkedModify (State.write (Pointee.repr (T := T)) q value)

attribute [rust_fun "core::ptr::write"] MutRawPtr.write

/-! ### Heap-model operations
Aeneas builds its models of Rust's raw-pointer functions (`from_mut`, `as_ptr`, `as_mut_ptr`,
`from_raw_parts`, `from_raw_parts_mut`) from the operations below, which act on the model's heap
directly. -/

/-- Transfers full cells into an exclusive borrow, blocking raw access to these cells. -/
def RawPtr.borrowRange (repr : Repr T) (q : RawPtr T) (count : Nat) : Result (List T) :=
  Result.checkedModify (State.borrowRange repr q count)

/-- `endBorrow` on the `values.length` cells from `q` on. -/
def RawPtr.endBorrowRange (repr : Repr T) (q : RawPtr T) (values : List T) : Result Unit :=
  Result.checkedModify (State.endBorrowRange repr q values)

def RawPtr.borrow (repr : Repr T) (q : RawPtr T) : Result T := do
  match ← q.borrowRange repr 1 with
  | [value] => .ok value
  | _ => .fail .undef

def RawPtr.endBorrow (repr : Repr T) (q : RawPtr T) (value : T) : Result Unit :=
  q.endBorrowRange repr [value]

/-- Raw-to-safe conversion with its matching effectful backward computation. -/
def RawPtr.borrowWithBack (repr : Repr T) (q : RawPtr T) :
    Result (T × (T → Result Unit)) :=
  Aeneas.Std.bind (q.borrow repr) fun value =>
    .ok (value, fun updated => q.endBorrow repr updated)

/-- A pure safe update followed by the matching return to raw memory. -/
def RawPtr.withBorrow (repr : Repr T) (q : RawPtr T) (update : T → T) : Result T :=
  Aeneas.Std.bind (q.borrowWithBack repr) fun (value, back) => do
    back (update value)
    pure value

def RawPtr.shareRange (repr : Repr T) (q : RawPtr T) (count : Nat) : Result (List T) :=
  Result.checkedModify (State.shareRange repr q count)

def RawPtr.endShareRange (repr : Repr T) (q : RawPtr T) (values : List T) : Result Unit :=
  Result.checkedModify (State.endShareRange repr q values)

/-- `read` on the `n` cells from `q` on. -/
def RawPtr.readRange (repr : Repr T) (q : RawPtr T) (count : Nat) : Result (List T) :=
  Result.checkedModify (State.readRange repr q count)

/-- Jointly choose an admissible encoding and compatible concrete placement. -/
def RawPtr.newBlock (repr : Repr T) (values : List T) (own : Bool) : Result (RawPtr T) :=
  Result.allocatingModify (State.newBlock repr values own)

/-- Exposes a safe mutable place, represented functionally without an address, as raw memory.
Used by `from_mut` and `as_mut_ptr`. The fresh block holds `values` with full access
and the matching backward computation removes it with `endExposure`. -/
def RawPtr.allocExposure (repr : Repr T) (values : List T) : Result (MutRawPtr T) :=
  RawPtr.newBlock repr values false

/-- Exposes a shared safe borrow with read-only cells (`shared 1`), as used by `as_ptr`.
Casting the returned pointer to mutable does not change those permissions. -/
def RawPtr.allocSharedExposure (repr : Repr T) (values : List T) : Result (ConstRawPtr T) :=
  Result.allocatingModify (State.newSharedExposure repr values)

def RawPtr.endExposure (repr : Repr T) (q : RawPtr T) (count : Nat) : Result Unit :=
  Result.checkedModify (State.removeExposure repr q count)

def RawPtr.endSharedExposure (repr : Repr T) (q : RawPtr T) (original : List T) : Result Unit :=
  Result.checkedModify (State.endSharedExposure repr q original)

/-- Exposes a shared borrow and returns its matching backward computation.
The backward computation checks the original value and retires the exposure. -/
def core.ptr.from_ref (repr : Repr T) (r : T) : Result (ConstRawPtr T × Result Unit) :=
  Aeneas.Std.bind (RawPtr.allocSharedExposure repr [r]) fun p =>
    .ok (p, p.endSharedExposure repr [r])

/-- Back function of `from_mut`: reads the value, with the writes made through the pointer, and
ends the exposure, so that the pointer can't be used anymore. -/
def core.ptr.end_from_mut [Pointee T] (p : MutRawPtr T) : Result T := do
  let value ← p.read
  p.endExposure (Pointee.repr (T := T)) 1
  .ok value

/-- Exposes `r` as raw memory; the back computation runs when the borrow ends. -/
@[rust_fun "core::ptr::from_mut" (statefulLifetimes := [0])]
def core.ptr.from_mut [Pointee T] (r : MutBorrow T) : Result (MutRawPtr T × Result T) :=
  Aeneas.Std.bind (RawPtr.allocExposure (Pointee.repr (T := T)) [r.val]) fun p =>
    .ok (p, core.ptr.end_from_mut p)

end Aeneas.Std
