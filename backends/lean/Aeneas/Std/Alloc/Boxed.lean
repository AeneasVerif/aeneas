/- `alloc::boxed`: `Box<T>` is `T` in the extracted Lean code, and `into_raw`/`from_raw` move the value
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
def alloc.boxed.Box.deref {T : Type _} (x : T) : T := x

@[expose, rust_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>, @T>}::deref_mut" -canFail (keepParams := [true, false])]
def alloc.boxed.Box.deref_mut {T : Type _} (x : T) : (T × (T → T)) := (x, λ x => x)

/-- Trait instance -/
@[expose, rust_trait_impl "core::ops::deref::Deref<Box<@T>, @T>" (keepParams := [true, false])]
def core.ops.deref.DerefBoxInst (T : Type _) :
  core.ops.deref.Deref T T := {
  deref x := ok (alloc.boxed.Box.deref x)
}

/-- Trait instance -/
@[expose, rust_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>" (keepParams := [true, false])]
def core.ops.deref.DerefMutBoxInst (T : Type _) :
  core.ops.deref.DerefMut T T := {
  derefInst := DerefBoxInst T
  deref_mut x := ok (alloc.boxed.Box.deref_mut x)
}

@[expose, rust_fun "alloc::boxed::{core::convert::AsMut<Box<@T>, @T>}::as_mut" -canFail (keepParams := [true,false])]
def alloc.boxed.AsMutBox.as_mut {T : Type _} (x : T) : T × (T → T) :=
  (x, fun x => x)

@[expose, reducible, rust_trait_impl "core::convert::AsMut<Box<@T>, @T>"]
def core.convert.AsMutBox (T : Type _) : core.convert.AsMut T T := {
  as_mut := fun x => ok (alloc.boxed.AsMutBox.as_mut x)
}

@[expose, rust_fun "alloc::boxed::{core::clone::Clone<Box<@T>>}::clone"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def alloc.boxed.CloneBox.clone {T : Type _} (cloneInst : core.clone.Clone T) : T → Result T :=
  cloneInst.clone

@[expose, reducible, rust_trait_impl "core::clone::Clone<Box<@T>>"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def core.clone.CloneBox {T : Type _} (cloneInst : core.clone.Clone T) : core.clone.Clone T := {
  clone := alloc.boxed.CloneBox.clone cloneInst
}

@[expose, rust_fun "alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}::eq" (keepParams := [true, false])]
def alloc.boxed.PartialEqBox.eq
  {T : Type _} (PartialEqInst : core.cmp.PartialEq T T) (x y : T) : Result Bool :=
  PartialEqInst.eq x y

@[expose, reducible, rust_trait_impl "core::cmp::PartialEq<Box<@T>, Box<@T>>" (keepParams := [true, false])]
def core.cmp.PartialEqBox {T : Type _} (PartialEqInst : core.cmp.PartialEq T T) :
  core.cmp.PartialEq T T := {
  eq := alloc.boxed.PartialEqBox.eq PartialEqInst
}

variable {H : Type (uh + 1)}

/-- Allocates a pointer using `Global.allocate`, as creating a Box in Rust would do --/
@[rust_fun "alloc::boxed::{Box<@T>}::into_raw"]
def alloc.boxed.Box.into_raw [Stores H T] (b : T) : ResultAt H (MutRawPtr T) :=
  alloc.alloc.Global.mk.allocate [b]

/-- Frees the `Box` using `Global.deallocate`, as dropping a Box in Rust would do --/
@[rust_fun "alloc::boxed::{Box<@T>}::from_raw"]
def alloc.boxed.Box.from_raw [Stores H T] (p : MutRawPtr T) : ResultAt H T :=
  Aeneas.Std.bind (RawPtr.read p) fun value =>
  Aeneas.Std.bind (alloc.alloc.Global.mk.deallocate p 1) fun () =>
  .ok value

end Aeneas.Std
