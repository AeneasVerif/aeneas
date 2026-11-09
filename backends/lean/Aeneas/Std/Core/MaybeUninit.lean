module

public import Aeneas.Std.Slice
public import Aeneas.Std.Core.Core

/-! # `MaybeUninit`

As in fournet/wip-memory-model, uninitialized memory exists only at the level of bytes
(`Byte.uninit`): `MaybeUninit T` has no representation (no `Repr` can tell an uninitialized value
from an initialized one, since decoding can't depend on uninitialized bytes). In safe code, a
`MaybeUninit T` is an `Option T`: `none` is uninitialized.

A `MaybeUninit T` (or a slice of them) is exposed as raw memory by `as_ptr`/`as_mut_ptr`, at the
address given by the placement, like the other safe places: an uninitialized value is exposed as
uninitialized bytes, and an initialized one as an encoding of its value, with the representation of
`T`. The pointer is a pointer to `MaybeUninit T`, which Rust code casts to a pointer to `T` (or to
bytes) before accessing the memory. When the exposure ends, the bytes of every element are read
back: an element whose bytes decode to a value of `T` is initialized with this value, and the other
ones are uninitialized. This forgets the bytes of the partially initialized elements: reading them
later fails, which is incomplete but sound. -/

@[expose] public section

namespace Aeneas.Std

@[rust_type "core::mem::maybe_uninit::MaybeUninit"]
structure core.mem.maybe_uninit.MaybeUninit (T : Type) where
  value : Option T

open core.mem.maybe_uninit

namespace State

/-- The bytes exposing a list of possibly uninitialized values at `address`: uninitialized bytes
for `none`, and an exposure of the value (see `State.exposes`) for `some`. -/
def exposesUninit (repr : Repr T) (s : State) (address : Nat) :
    List (MaybeUninit T) → List (Vector Byte repr.size) → Prop
  | [], [] => True
  | ⟨none⟩ :: values, bytes :: data =>
      bytes = Vector.replicate repr.size .uninit ∧ exposesUninit repr s (address + repr.size) values data
  | ⟨some value⟩ :: values, bytes :: data =>
      exposes repr s address value bytes ∧ exposesUninit repr s (address + repr.size) values data
  | _, _ => False

/-- Exposure of a list of possibly uninitialized values at `address`. -/
def exposeUninitAt (repr : Repr T) (values : List (MaybeUninit T)) (address : BasePtr) (s₀ : State)
    (p : RawPtr (MaybeUninit T)) (s₁ : State) : Prop :=
  ∃ data root, exposesUninit repr s₀ address.val values data ∧
    Heap.newBlock repr data false address root s₀ = some (p.cast T, s₁)

/-- Shared exposure of a list of possibly uninitialized values at `address`. -/
def sharedExposeUninitAt (repr : Repr T) (values : List (MaybeUninit T)) (address : BasePtr)
    (s₀ : State) (p : RawPtr (MaybeUninit T)) (s₁ : State) : Prop :=
  ∃ data root, exposesUninit repr s₀ address.val values data ∧
    Heap.newSharedExposure repr data address root s₀ = some (p.cast T, s₁)

end State

/-- The values of the `count` elements from `p` on, read back from their bytes: an element whose
bytes decode to a value is initialized with this value. Fails if a byte can't be read (for
instance, because it is still exclusively borrowed). -/
def Heap.readUninitRange (repr : Repr T) (p : RawPtr T) (count : Nat) (s : Heap) :
    Option (List (MaybeUninit T)) := do
  let block ← s.allocations p.provenance
  if s.live block && block.bptr.val ≤ p.address.val && repr.align.val ∣ p.address.val &&
      p.address.val + count * repr.size ≤ block.bptr.val + block.repr.length then
    (List.range count).mapM fun i =>
      let offset := p.offsetFrom block.bptr + i * repr.size
      if h : offset + repr.size ≤ block.repr.length then
        (Repr.readBytes repr.size (repr.select block.bytes offset h)).map fun bytes =>
          ⟨repr.decode bytes⟩
      else none
  else none

/-- Ends a mutable exposure of possibly uninitialized values: reads them back and removes the
exposure. -/
def RawPtr.endUninitExposure (repr : Repr T) (p : RawPtr (MaybeUninit T)) (count : Nat) :
    Result (List (MaybeUninit T)) := do
  let values ← Result.checkedModify fun s values s' =>
    Heap.readUninitRange repr (p.cast T) count s = some values ∧ s' = s
  (p.cast T).endExposure repr count
  .ok values

/-- Ends a shared exposure of possibly uninitialized values: the exposure can't have been
modified. -/
def RawPtr.endSharedUninitExposure (repr : Repr T) (p : RawPtr (MaybeUninit T))
    (original : List (MaybeUninit T)) : Result Unit :=
  Result.checkedModify fun s _ s' =>
    Heap.readUninitRange repr (p.cast T) original.length s = some original ∧
      Heap.endSharedExposure repr (p.cast T) original.length s = some s'

def MaybeUninit.allocExposure (repr : Repr T) (values : List (MaybeUninit T)) (address : BasePtr) :
    Result (MutRawPtr (MaybeUninit T)) :=
  Result.allocatingModify (State.exposeUninitAt repr values address)

def MaybeUninit.allocSharedExposure (repr : Repr T) (values : List (MaybeUninit T))
    (address : BasePtr) : Result (ConstRawPtr (MaybeUninit T)) :=
  Result.allocatingModify (State.sharedExposeUninitAt repr values address)

/-- Slices of `MaybeUninit T` are exposed with the representation of `T`. -/
instance MaybeUninit.Insts.Exposable {T : Type} [Pointee T] : Exposable (MaybeUninit T) where
  as_ptr address s :=
    Aeneas.Std.bind (MaybeUninit.allocSharedExposure (Pointee.repr (T := T)) s.val.val address)
      fun p => .ok (p, p.endSharedUninitExposure (Pointee.repr (T := T)) s.val.val)
  as_mut_ptr address s :=
    Aeneas.Std.bind (MaybeUninit.allocExposure (Pointee.repr (T := T)) s.val.val address)
      fun p => .ok (p, do
        let values ← p.endUninitExposure (Pointee.repr (T := T)) s.val.length
        if h : values.length ≤ Usize.max then .ok (Slice.from values h) else .fail .undef)

namespace core.mem.maybe_uninit.MaybeUninit

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::uninit"]
def uninit (T : Type) : Result (MaybeUninit T) := .ok ⟨none⟩

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::new"]
def new {T : Type} (value : T) : Result (MaybeUninit T) := .ok ⟨some value⟩

/-- Undefined behavior if the value is uninitialized. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::assume_init"]
def assume_init {T : Type} (x : MaybeUninit T) : Result T :=
  match x.value with
  | some value => .ok value
  | none => .fail .undef

/-- Exposes the value as raw memory at `address` (an uninitialized value as uninitialized bytes);
the back computation reads it back when the borrow ends. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::as_mut_ptr"
  (statefulLifetimes := [0]) (placement := true)]
def as_mut_ptr {T : Type} [Pointee T] (address : BasePtr) (self : MutBorrow (MaybeUninit T)) :
    Result (MutRawPtr T × Result (MaybeUninit T)) :=
  Aeneas.Std.bind (MaybeUninit.allocExposure (Pointee.repr (T := T)) [self.val] address) fun p =>
    .ok (p.cast T, do
      match ← p.endUninitExposure (Pointee.repr (T := T)) 1 with
      | [value] => .ok value
      | _ => .fail .undef)

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::as_ptr"
  (statefulLifetimes := [0]) (placement := true)]
def as_ptr {T : Type} [Pointee T] (address : BasePtr) (self : SharedBorrow (MaybeUninit T)) :
    Result (ConstRawPtr T × Result Unit) :=
  Aeneas.Std.bind (MaybeUninit.allocSharedExposure (Pointee.repr (T := T)) [self.val] address)
    fun p => .ok (p.cast T, p.endSharedUninitExposure (Pointee.repr (T := T)) [self.val])

@[rust_fun
  "core::mem::maybe_uninit::{core::clone::Clone<core::mem::maybe_uninit::MaybeUninit<@T>>}::clone"]
def Insts.CoreCloneClone.clone {T : Type} (_ : core.marker.Copy T) (self : SharedBorrow (MaybeUninit T)) :
    Result (MaybeUninit T) :=
  .ok self.val

end core.mem.maybe_uninit.MaybeUninit

end Aeneas.Std
