/- `alloc::boxed`: `Box<T>` is the wrapper `Box T` in the extracted Lean code, and `into_raw`/`from_raw` move the value
into and out of a allocation of the global allocator. -/
module
public import Aeneas.Std.Alloc.Alloc
public import Aeneas.Std.Core.Ptr
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Convert
public section

namespace Aeneas.Std

open Result

@[expose, rust_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>, @T>}::deref" -canFail (keepParams := [true, false])]
def alloc.boxed.Box.deref {T : Type _} (x : SharedBorrow (Box T)) : SharedBorrow T :=
  SharedBorrow.mk x.val.val

@[expose, rust_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>, @T>}::deref_mut" -canFail (keepParams := [true, false])]
def alloc.boxed.Box.deref_mut {T : Type _} (x : MutBorrow (Box T)) :
  MutBorrow T × (T → Box T) :=
  (MutBorrow.mk x.val.val, λ x => Box.mk x)

/-- Trait instance -/
@[expose, rust_trait_impl "core::ops::deref::Deref<Box<@T>, @T>" (keepParams := [true, false])]
def core.ops.deref.DerefBoxInst (T : Type _) :
  core.ops.deref.Deref (Box T) T := {
  deref x := ok (alloc.boxed.Box.deref x)
}

/-- Trait instance -/
@[expose, rust_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>" (keepParams := [true, false])]
def core.ops.deref.DerefMutBoxInst (T : Type _) :
  core.ops.deref.DerefMut (Box T) T := {
  derefInst := DerefBoxInst T
  deref_mut x := ok (alloc.boxed.Box.deref_mut x)
}

@[expose, rust_fun "alloc::boxed::{core::convert::AsMut<Box<@T>, @T>}::as_mut" -canFail (keepParams := [true,false])]
def alloc.boxed.AsMutBox.as_mut {T : Type _} (x : MutBorrow (Box T)) :
  MutBorrow T × (T → Box T) :=
  (MutBorrow.mk x.val.val, fun x => Box.mk x)

@[expose, reducible, rust_trait_impl "core::convert::AsMut<Box<@T>, @T>"]
def core.convert.AsMutBox (T : Type _) : core.convert.AsMut (Box T) T := {
  as_mut := fun x => ok (alloc.boxed.AsMutBox.as_mut x)
}

@[expose, rust_fun "alloc::boxed::{core::clone::Clone<Box<@T>>}::clone"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def alloc.boxed.CloneBox.clone {T : Type _} (cloneInst : core.clone.Clone T)
  (x : SharedBorrow (Box T)) : Result (Box T) := do
  let y ← cloneInst.clone (SharedBorrow.mk x.val.val)
  ok (Box.mk y)

@[expose, reducible, rust_trait_impl "core::clone::Clone<Box<@T>>"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def core.clone.CloneBox {T : Type _} (cloneInst : core.clone.Clone T) :
  core.clone.Clone (Box T) := {
  clone := alloc.boxed.CloneBox.clone cloneInst
}

@[expose, rust_fun "alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}::eq" (keepParams := [true, false])]
def alloc.boxed.PartialEqBox.eq
  {T : Type _} (PartialEqInst : core.cmp.PartialEq T T) (x y : SharedBorrow (Box T)) :
  Result Bool :=
  PartialEqInst.eq (SharedBorrow.mk x.val.val) (SharedBorrow.mk y.val.val)

@[expose, reducible, rust_trait_impl "core::cmp::PartialEq<Box<@T>, Box<@T>>" (keepParams := [true, false])]
def core.cmp.PartialEqBox {T : Type _} (PartialEqInst : core.cmp.PartialEq T T) :
  core.cmp.PartialEq (Box T) (Box T) := {
  eq := alloc.boxed.PartialEqBox.eq PartialEqInst
}

/-- Moves the value of the box into memory, in a block with allocation cleanup authority.
In Rust, `into_raw` doesn't
call the global allocator: the box was already allocated by `Box::new`, and `into_raw` only converts
the pointer. But the model of `Box<T>` is the wrapper `Box T`, which has no address, so the block is created here,
using `RawPtr.newBlock`, jointly choosing compatible placement and encoding.
Ghost Nat IDs cannot exhaust. Conversion can still fail if the explicit heap has
no compatible placement; safe-boundary feasibility is an additional assumption,
not a Rust precondition. The functional Box representation does not preserve
address identity across repeated conversions. -/
@[rust_fun "alloc::boxed::{Box<@T>}::into_raw"]
def alloc.boxed.Box.into_raw (repr : Repr T) (b : Box T) : Result (MutRawPtr T) :=
  RawPtr.newBlock repr [b.val] true

/-- Moves the value out of explicit memory with `State.returnOwned`, without physical death.
In Rust, `from_raw` doesn't call the global allocator either: it only converts the pointer, and
the memory is freed when the box is dropped. But the model of `Box<T>` is the wrapper `Box T`, so the value can't
stay explicitly active. Immutable metadata retains the old pointer's address, but converting
the same Box back to raw still forgets its safe-place identity in this prototype. -/
@[rust_fun "alloc::boxed::{Box<@T>}::from_raw"]
def alloc.boxed.Box.from_raw (repr : Repr T) (p : MutRawPtr T) : Result (Box T) := do
  let value ← RawPtr.read repr p
  Result.checkedModify (State.returnOwned repr p 1)
  pure ⟨value⟩

end Aeneas.Std
