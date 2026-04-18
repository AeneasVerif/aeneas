import Lean
import Aeneas.Std.Primitives
import Aeneas.Tactic.Step.Init
import Aeneas.Std.Alloc
import Aeneas.Std.Core.Cmp
import Aeneas.Std.Core.Default
import Aeneas.Std.Core.Result

namespace Aeneas

namespace Std

open Result

attribute [rust_type "core::option::Option" -prefixVariantNames] Option
attribute [step_simps] Result.ofOption

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
@[reducible, simp, step_simps]
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
@[simp, step_simps, rust_fun "core::mem::replace" (canFail := false) (lift := false)]
def mem.replace {a : Type} (dst : a) (src : a) : a × a := (dst, src)

/- [core::mem::swap] -/
@[simp, step_simps, rust_fun "core::mem::swap" (canFail := false) (lift := false)]
def mem.swap {T : Type} (a b : T): T × T := (b, a)

end core

/-- Builtin clone implementation (used for some builtin types) -/
def BuiltinClone (Self : Type) : core.clone.Clone Self where
  clone := .ok
  clone_from := fun _ x => .ok x

/-- Builtin clone implementation (used for some builtin types) -/
def BuiltinCopy (Self : Type) : core.marker.Copy Self where
  cloneInst := BuiltinClone Self

@[simp, step_simps, rust_fun "core::option::{core::option::Option<@T>}::unwrap"]
def core.option.Option.unwrap {T : Type} (x : Option T) : Result T :=
  Result.ofOption x Error.panic

@[step_pure_def, rust_fun "core::option::{core::option::Option<@T>}::unwrap_or" -canFail]
def core.option.Option.unwrap_or (self : Option T) (default : T) : T :=
  match self with
  | none => default
  | some self => self

@[simp] def core.option.Option.unwrap_or_some (self default : T) :
  core.option.Option.unwrap_or (some self) default = self := by simp [unwrap_or]

@[simp] def core.option.Option.unwrap_or_none (default : T) :
  core.option.Option.unwrap_or none default = default := by simp [unwrap_or]

@[simp, step_simps, rust_fun "core::option::{core::option::Option<@T>}::take" -canFail -lift]
def core.option.Option.take {T: Type} (self: Option T): Option T × Option T := (self, .none)

@[simp, step_simps, rust_fun "core::option::{core::option::Option<@T>}::is_none" -canFail -lift]
def core.option.Option.is_none {T: Type} (self: Option T): Bool := self.isNone

/-! ## `Option<T>` methods

Pinned to Rust `1.85.0` (Charon pin `nightly-2026-02-07` — these methods are
stable and unchanged across recent versions). -/

/-- `Option::as_ref`: converts `&Option<T>` to `Option<&T>`. In Aeneas,
references are erased, so this is the identity.

- Docs: https://doc.rust-lang.org/core/option/enum.Option.html#method.as_ref
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs
-/
@[simp, step_simps, rust_fun "core::option::{core::option::Option<@T>}::as_ref" -canFail -lift]
def core.option.Option.as_ref {T : Type} (self : Option T) : Option T := self

/-- `Option::ok_or`: transforms `Option<T>` into `Result<T, E>` — `Some(v)` maps
to `Ok(v)`, `None` maps to `Err(err)`.

- Docs: https://doc.rust-lang.org/core/option/enum.Option.html#method.ok_or
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs
-/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or" -canFail -lift]
def core.option.Option.ok_or {T : Type} {E : Type}
    (self : Option T) (err : E) : core.result.Result T E :=
  match self with
  | some v => .Ok v
  | none => .Err err

@[simp] theorem core.option.Option.ok_or_some {T E : Type} (v : T) (err : E) :
    core.option.Option.ok_or (some v) err = .Ok v := by rfl

@[simp] theorem core.option.Option.ok_or_none {T E : Type} (err : E) :
    core.option.Option.ok_or (none : Option T) err = .Err err := by rfl

/-- `PartialEq for Option<T>::eq`: `true` iff both are `None`, or both are
`Some` and their contents are equal under the provided `PartialEq<T>`.

- Docs: https://doc.rust-lang.org/core/option/enum.Option.html#impl-PartialEq-for-Option%3CT%3E
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs
-/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type}
    (PartialEqInst : core.cmp.PartialEq T T)
    (self : Option T) (other : Option T) : Result Bool :=
  match self, other with
  | none, none => .ok true
  | some a, some b => PartialEqInst.eq a b
  | _, _ => .ok false

@[reducible, rust_trait_impl
  "core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>"]
def core.option.Option.Insts.CoreCmpPartialEqOption {T : Type}
    (PartialEqInst : core.cmp.PartialEq T T) :
    core.cmp.PartialEq (Option T) (Option T) := {
  eq := core.option.Option.Insts.CoreCmpPartialEqOption.eq PartialEqInst
}

/-- `Default for Option<T>::default`: returns `None`.

- Docs: https://doc.rust-lang.org/core/option/enum.Option.html#impl-Default-for-Option%3CT%3E
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs
-/
@[rust_fun
  "core::option::{core::default::Default<core::option::Option<@T>>}::default"]
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type) :
    Result (Option T) := .ok none

@[reducible, rust_trait_impl
  "core::default::Default<core::option::Option<@T>>"]
def core.option.Option.Insts.CoreDefaultDefault (T : Type) :
    core.default.Default (Option T) := {
  default := core.option.Option.Insts.CoreDefaultDefault.default T
}

/-- `Clone for Option<T>::clone`: clones each variant. `None` clones to `None`;
`Some(v)` clones to `Some(v')` where `v'` is the clone of `v` under the
provided `Clone<T>`.

- Docs: https://doc.rust-lang.org/core/option/enum.Option.html#impl-Clone-for-Option%3CT%3E
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs
-/
@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone {T : Type}
    (CloneInst : core.clone.Clone T)
    (self : Option T) : Result (Option T) :=
  match self with
  | none => .ok none
  | some v => do
    let v' ← CloneInst.clone v
    .ok (some v')

@[reducible, rust_trait_impl
  "core::clone::Clone<core::option::Option<@T>>"]
def core.option.Option.Insts.CoreCloneClone {T : Type}
    (CloneInst : core.clone.Clone T) :
    core.clone.Clone (Option T) := {
  clone := core.option.Option.Insts.CoreCloneClone.clone CloneInst
  clone_from := fun _ x => core.option.Option.Insts.CoreCloneClone.clone CloneInst x
}

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
