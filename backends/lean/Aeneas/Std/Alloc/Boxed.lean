/- `alloc::boxed`: `Box<T>` is `T` in the extracted code, and `into_raw`/`from_raw` move the value
into and out of a one-slot allocation of the global allocator: "For non-zero-sized values, a `Box`
will use the `Global` allocator for its allocation"
([memory layout](https://doc.rust-lang.org/std/boxed/index.html#memory-layout)). Zero-sized values
are not special-cased: they get a slot too. -/
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

@[rust_fun "alloc::boxed::{Box<@T>}::into_raw"]
def alloc.boxed.Box.into_raw (b : T) : Result (MutRawPtr T) :=
  Global.mk.allocate [b]

/-- Moves the value out and frees the `Box`, as dropping it does: `Global.deallocate` with
`Layout::for_value(&*p)`, one slot. So `p` must be a pointer returned by `into_raw`. See the safety
section of [`Box::from_raw`](https://doc.rust-lang.org/std/boxed/struct.Box.html#method.from_raw).
-/
@[rust_fun "alloc::boxed::{Box<@T>}::from_raw"]
def alloc.boxed.Box.from_raw (p : MutRawPtr T) : Result T := do
  let value ← RawPtr.read p
  Global.mk.deallocate p 1
  pure value

end Aeneas.Std
