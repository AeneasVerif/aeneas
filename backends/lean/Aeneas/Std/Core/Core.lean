import Lean
import Aeneas.Std.Primitives
import Aeneas.Progress.Init
import Aeneas.Std.Alloc

namespace Aeneas

namespace Std

open Result

attribute [rust_type "core::option::Option" -prefixVariantNames] Option

@[rust_fun "alloc::boxed::{core::convert::AsMut<Box<@T>, @T>}::as_mut" -canFail (keepParams := [true,false])]
def alloc.boxed.AsMutBox.as_mut {T : Type} (x : T) : T × (T → T) :=
  (x, fun x => x)

namespace core

@[rust_trait "core::convert::From" (methodsInfo := [⟨ "from", "from_" ⟩])]
structure convert.From (Self T : Type) where
  from_ : T → Result Self

@[rust_trait "core::clone::Clone" (defaultMethods := ["clone_from"])]
structure clone.Clone (Self : Type) where
  clone : Self → Result Self
  clone_from : Self → Self → Result Self := fun _ => clone

def clone.Clone.from_from.default {Self : Type} (clone : Self → Result Self)
  (_self source : Self) : Result Self :=
  clone source

@[reducible, rust_trait_impl "core::clone::Clone<alloc::alloc::Global>"]
def core.clone.CloneGlobal : core.clone.Clone Global := {
  clone := alloc.alloc.CloneGlobal.clone
}

/- [core::clone::impls::{(core::clone::Clone for bool)#19}::clone] -/
@[reducible, simp, progress_simps]
def clone.impls.CloneBool.clone (b : Bool) : Bool := b

@[reducible, rust_trait_impl "core::clone::Clone<bool>"]
def clone.CloneBool : clone.Clone Bool := {
  clone := fun b => ok (clone.impls.CloneBool.clone b)
  clone_from := fun _ b => ok (clone.impls.CloneBool.clone b)
}

@[rust_fun "alloc::boxed::{core::clone::Clone<Box<@T>>}::clone"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def alloc.boxed.CloneBox.clone {T : Type} (cloneInst : core.clone.Clone T) : T → Result T :=
  cloneInst.clone

@[reducible, rust_trait_impl "core::clone::Clone<Box<@T>>"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def core.clone.CloneBox {T : Type} (cloneInst : core.clone.Clone T) : core.clone.Clone T := {
  clone := alloc.boxed.CloneBox.clone cloneInst
}

@[rust_trait "core::marker::Copy" (parentClauses := ["cloneInst"])]
structure marker.Copy (Self : Type) where
  cloneInst : core.clone.Clone Self

@[reducible, rust_trait_impl "core::marker::Copy<bool>"]
def core.marker.CopyBool : core.marker.Copy Bool := {
  cloneInst := core.clone.CloneBool
}

/- [core::mem::replace]

   This acts like a swap effectively in a functional pure world.
   We return the old value of `dst`, i.e. `dst` itself.
   The new value of `dst` is `src`. -/
@[simp, progress_simps, rust_fun "core::mem::replace" (canFail := false) (lift := false)]
def mem.replace {a : Type} (dst : a) (src : a) : a × a := (dst, src)

/- [core::mem::swap] -/
@[simp, progress_simps, rust_fun "core::mem::swap" (canFail := false) (lift := false)]
def mem.swap {T : Type} (a b : T): T × T := (b, a)

end core

/-- Builtin clone implementation (used for some builtin types) -/
def BuiltinClone (Self : Type) : core.clone.Clone Self where
  clone := .ok
  clone_from := fun _ x => .ok x

/-- Builtin clone implementation (used for some builtin types) -/
def BuiltinCopy (Self : Type) : core.marker.Copy Self where
  cloneInst := BuiltinClone Self

@[simp, progress_simps, rust_fun "core::option::{core::option::Option<@T>}::unwrap"]
def core.option.Option.unwrap {T : Type} (x : Option T) : Result T :=
  Result.ofOption x Error.panic

@[progress_pure_def, rust_fun "core::option::{core::option::Option<@T>}::unwrap_or" -canFail]
def core.option.Option.unwrap_or (self : Option T) (default : T) : T :=
  match self with
  | none => default
  | some self => self

@[simp] def core.option.Option.unwrap_or_some (self default : T) :
  core.option.Option.unwrap_or (some self) default = self := by simp [unwrap_or]

@[simp] def core.option.Option.unwrap_or_none (default : T) :
  core.option.Option.unwrap_or none default = default := by simp [unwrap_or]

@[simp, progress_simps, rust_fun "core::option::{core::option::Option<@T>}::take" -canFail -lift]
def core.option.Option.take {T: Type} (self: Option T): Option T × Option T := (self, .none)

@[simp, progress_simps, rust_fun "core::option::{core::option::Option<@T>}::is_none" -canFail -lift]
def core.option.Option.is_none {T: Type} (self: Option T): Bool := self.isNone

@[rust_type "core::ops::range::RangeFrom"]
structure core.ops.range.RangeFrom (Idx : Type) where
  start : Idx

@[rust_type "core::panicking::AssertKind"]
inductive core.panicking.AssertKind where
| Eq : core.panicking.AssertKind
| Ne : core.panicking.AssertKind
| Match : core.panicking.AssertKind

@[rust_fun "core::clone::impls::{core::clone::Clone<&'0 @T>}::clone"]
def core.clone.impls.CloneShared.clone {T : Type} (x : T) : Result T := .ok x

end Std

end Aeneas
