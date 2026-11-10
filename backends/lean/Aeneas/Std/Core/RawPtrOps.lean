module

public import Aeneas.Std.Core.PtrMovement
public import Aeneas.Std.Scalar.Notations

/-! Models of raw-pointer functions used by Ryu and Zmij: casts, `sub`, unaligned accesses, copies,
`write_bytes`, `null_mut`, and `size_of`/`align_of`. They are built from the operations of the byte
heap model (`Heap.copyBytes`, `State.offset`, `State.read`, `State.write`). -/

@[expose] public section

namespace Aeneas.Std

/-- Thin raw-pointer casts preserve the allocation and the address: they change neither bytes nor
permissions (accesses check the alignment, bounds, permissions and decoding). -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast"]
def RawPtr.ptr_cast {T : Type} (U : Type) (q : RawPtr T) : Result (RawPtr U) :=
  .ok (RawPtr.cast U q)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::cast"] RawPtr.ptr_cast

/-- `<*mut T>::sub`, `<*const T>::sub`: `count` elements backwards, within the allocation. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::sub"]
def RawPtr.sub [Pointee T] (q : RawPtr T) (count : Usize) : Result (RawPtr T) :=
  Result.checkedModify (State.offset (Pointee.repr (T := T)) q (-(count.val : Int)))

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::sub"] RawPtr.sub

/-- The representation of `T` without alignment constraint, for the unaligned accesses. -/
def Repr.unaligned (repr : Repr T) : Repr T :=
  { repr with align := ⟨1, 0, rfl⟩, aligned := Nat.one_dvd _ }

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write_unaligned"]
def MutRawPtr.write_unaligned [Pointee T] (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.checkedModify (State.write (Pointee.repr (T := T)).unaligned q value)

attribute [rust_fun "core::ptr::write_unaligned"] MutRawPtr.write_unaligned

@[rust_fun "core::ptr::const_ptr::{*const @T}::read_unaligned"]
def RawPtr.read_unaligned [Pointee T] (q : RawPtr T) : Result T :=
  Result.checkedModify (State.read (Pointee.repr (T := T)).unaligned q)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read_unaligned"] RawPtr.read_unaligned
attribute [rust_fun "core::ptr::read_unaligned"] RawPtr.read_unaligned

/-- `count` elements of `T`, in bytes; undefined behavior if it doesn't fit `isize`. -/
def RawPtr.byteCount [Pointee T] (count : Usize) : Result Nat :=
  let n := count.val * (Pointee.repr (T := T)).size
  if (n : Int) ≤ IScalar.cMax .Isize then .ok n else .fail .undef

/-- `ptr::copy`: memmove of `count` elements, preserving the initialization and the pointer bytes.
Both pointers must be aligned. -/
@[rust_fun "core::ptr::copy"]
def core.ptr.copy [Pointee T] (src : ConstRawPtr T) (dst : MutRawPtr T) (count : Usize) :
    Result Unit := do
  let n ← RawPtr.byteCount (T := T) count
  let align := (Pointee.repr (T := T)).align.val
  if align ∣ src.address.val ∧ align ∣ dst.address.val then
    Result.checkedModify fun s _ s' => Heap.copyBytes src dst n s = some s'
  else .fail .undef

/-- `ptr::copy_nonoverlapping`: `ptr::copy`, and the two ranges can't overlap. -/
@[rust_fun "core::ptr::copy_nonoverlapping"]
def core.ptr.copy_nonoverlapping [Pointee T] (src : ConstRawPtr T) (dst : MutRawPtr T)
    (count : Usize) : Result Unit := do
  let n ← RawPtr.byteCount (T := T) count
  if src.address.val + n ≤ dst.address.val ∨ dst.address.val + n ≤ src.address.val then
    core.ptr.copy src dst count
  else .fail .undef

/-- Writes `n` times the byte `byte`, from `q` on. -/
def MutRawPtr.writeBytes (q : MutRawPtr U8) (byte : U8) : Nat → Result Unit
  | 0 => .ok ()
  | n + 1 => do
    MutRawPtr.write q byte
    if n = 0 then .ok ()
    else
      let q' ← RawPtr.add q 1#usize
      MutRawPtr.writeBytes q' byte n

/-- `ptr::write_bytes`: sets `count * size_of::<T>()` bytes to `byte`; the pointer must be aligned. -/
@[rust_fun "core::ptr::write_bytes"]
def core.ptr.write_bytes [Pointee T] (dst : MutRawPtr T) (byte : U8) (count : Usize) :
    Result Unit := do
  let n ← RawPtr.byteCount (T := T) count
  if (Pointee.repr (T := T)).align.val ∣ dst.address.val then
    MutRawPtr.writeBytes (RawPtr.cast U8 dst) byte n
  else .fail .undef

/-- The null pointer: no allocation contains the address `0`, so it can't be accessed or offset. -/
@[rust_fun "core::ptr::null_mut"]
def core.ptr.null_mut (T : Type) : Result (MutRawPtr T) := .ok ⟨0, 0#usize⟩

@[rust_fun "core::ptr::null"]
def core.ptr.null (T : Type) : Result (ConstRawPtr T) := .ok ⟨0, 0#usize⟩

/-- `size_of::<T>()`: the size of the representation of `T` (`Pointee.Calibrated` relates it to the
Rust layout). -/
@[rust_fun "core::mem::size_of"]
def core.mem.size_of (T : Type) [Pointee T] : Result Usize :=
  let n := (Pointee.repr (T := T)).size
  if _h : n ≤ Usize.max then .ok ⟨BitVec.ofNat _ n⟩ else .fail .undef

@[rust_fun "core::mem::align_of"]
def core.mem.align_of (T : Type) [Pointee T] : Result Usize :=
  let n := (Pointee.repr (T := T)).align.val
  if _h : n ≤ Usize.max then .ok ⟨BitVec.ofNat _ n⟩ else .fail .undef

end Aeneas.Std

namespace Aeneas.Std

/-- `&*p`: a shared reborrow of the value behind a raw pointer (introduced by the pre-pass
`decompose_raw_ptr_derefs`). As for `from_raw_parts`, the cell is shared while the borrow is live:
writing it through any pointer is then undefined behavior (`fail .undef`), as in Rust. The backward
computation ends the share when the lifetime of the borrow ends. -/
@[rust_fun "core::ptr::const_ptr::{*const @T}::as_ref_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_ref_unchecked [Pointee T] (q : RawPtr T) : Result (SharedBorrow T × Result Unit) :=
  Aeneas.Std.bind (q.shareRange (Pointee.repr (T := T)) 1) fun values =>
  match values with
  | [value] => .ok (⟨value⟩, q.endShareRange (Pointee.repr (T := T)) [value])
  | _ => .fail .undef

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::as_ref_unchecked" (statefulLifetimes := [0])]
  RawPtr.as_ref_unchecked

/-- `&mut *p`: the value is exclusively borrowed from the heap (raw accesses to its cells fail)
until the borrow ends, when the backward computation writes the final value back. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::as_mut_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_mut_unchecked [Pointee T] (q : MutRawPtr T) :
    Result (MutBorrow T × (T → Result Unit)) := do
  let (value, back) ← RawPtr.borrowWithBack (Pointee.repr (T := T)) q
  .ok (⟨value⟩, back)

/-- `ptr::from_ref` (and the raw borrows `&raw const p` of places): exposes the shared borrow as
read-only raw memory at `address`, until the borrow ends. -/
@[rust_fun "core::ptr::from_ref" (statefulLifetimes := [0]) (placement := true)]
def core.ptr.from_ref_model [Pointee T] (address : BasePtr) (r : SharedBorrow T) :
    Result (ConstRawPtr T × Result Unit) :=
  core.ptr.from_ref (Pointee.repr (T := T)) address r.val

end Aeneas.Std
