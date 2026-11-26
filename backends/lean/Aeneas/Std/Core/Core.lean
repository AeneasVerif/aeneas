module
public import Lean
public import Aeneas.Std.Primitives
public meta import Aeneas.Tactic.Step.Init
public import Aeneas.Tactic.Elab.TraitDefault.Init
public section

namespace Aeneas

namespace Std

open Result

attribute [rust_type "core::option::Option" -prefixVariantNames] Option

namespace core

@[rust_trait "core::convert::From"]
structure convert.From (Self T : Type _) where
  «from» : T → Result Self

@[rust_trait "core::clone::Clone" (defaultMethods := ["clone_from"])]
structure clone.Clone (Self : Type _) where
  clone : Self → Result Self
  clone_from : Self → Self → Result Self := fun _ => clone

@[expose, trait_default]
def clone.Clone.clone_from.default {Self : Type _} (CloneInst : core.clone.Clone Self)
  (_self source : Self) : Result Self :=
  CloneInst.clone source

/- [core::clone::impls::{(core::clone::Clone for bool)#19}::clone] -/
@[expose, reducible, simp, step_simps]
def clone.impls.CloneBool.clone (b : Bool) : Bool := b

@[expose, reducible, rust_trait_impl "core::clone::Clone<bool>"]
def clone.CloneBool : clone.Clone Bool := {
  clone := fun b => ok (clone.impls.CloneBool.clone b)
  clone_from := fun _ b => ok (clone.impls.CloneBool.clone b)
}

@[rust_trait "core::marker::Copy" (parentClauses := ["cloneInst"])]
structure marker.Copy (Self : Type _) where
  cloneInst : core.clone.Clone Self

@[expose, reducible, rust_trait_impl "core::marker::Copy<bool>"]
def marker.CopyBool : core.marker.Copy Bool := {
  cloneInst := core.clone.CloneBool
}

/- [core::mem::replace]

   This acts like a swap effectively in a functional pure world.
   We return the old value of `dst`, i.e. `dst` itself.
   The new value of `dst` is `src`. -/
@[expose, simp, step_simps, rust_fun "core::mem::replace" (canFail := false) (lift := false)]
def mem.replace {a : Type _} (dst : a) (src : a) : a × a := (dst, src)

/- [core::mem::swap] -/
@[expose, simp, step_simps, rust_fun "core::mem::swap" (canFail := false) (lift := false)]
def mem.swap {T : Type _} (a b : T): T × T := (b, a)

end core

/-- Builtin clone implementation (used for some builtin types) -/
def BuiltinClone (Self : Type _) : core.clone.Clone Self where
  clone := .ok
  clone_from := fun _ x => .ok x

/-- Builtin clone implementation (used for some builtin types) -/
def BuiltinCopy (Self : Type _) : core.marker.Copy Self where
  cloneInst := BuiltinClone Self

@[expose, rust_fun "core::option::{core::option::Option<@T>}::unwrap"]
def core.option.Option.unwrap {T : Type _} (x : Option T) : Result T :=
  Result.ofOption x Error.panic

@[step]
theorem core.option.Option.unwrap.spec {T : Type _} (x : Option T) (h : x.isSome) :
  unwrap x ⦃ v => x = some v ⦄ := by
  simp only [unwrap, ofOption]; grind

@[expose, step_pure_def, rust_fun "core::option::{core::option::Option<@T>}::unwrap_or" -canFail]
def core.option.Option.unwrap_or (self : Option T) (default : T) : T :=
  match self with
  | none => default
  | some self => self

@[simp] theorem core.option.Option.unwrap_or_some (self default : T) :
  core.option.Option.unwrap_or (some self) default = self := by simp [unwrap_or]

@[simp] theorem core.option.Option.unwrap_or_none (default : T) :
  core.option.Option.unwrap_or none default = default := by simp [unwrap_or]

@[expose, simp, step_simps, rust_fun "core::option::{core::option::Option<@T>}::take" -canFail -lift]
def core.option.Option.take {T: Type _} (self: Option T): Option T × Option T := (self, .none)

@[expose, simp, step_simps, rust_fun "core::option::{core::option::Option<@T>}::is_none" -canFail -lift]
def core.option.Option.is_none {T: Type _} (self: Option T): Bool := self.isNone

/-- Returns `true` if the option is `some`. -/
@[expose, simp, step_simps, rust_fun "core::option::{core::option::Option<@T>}::is_some" -canFail -lift]
def core.option.Option.is_some {T: Type _} (self: Option T): Bool := self.isSome

@[rust_type "core::ops::range::RangeFrom"]
structure core.ops.range.RangeFrom (Idx : Type _) where
  start : Idx

@[rust_type "core::panicking::AssertKind"]
inductive core.panicking.AssertKind where
| Eq : core.panicking.AssertKind
| Ne : core.panicking.AssertKind
| Match : core.panicking.AssertKind

@[expose, rust_fun "core::clone::impls::{core::clone::Clone<&'0 @T>}::clone"]
def core.clone.impls.CloneShared.clone {T : Type _} (x : T) : Result T := .ok x

/-! Models of the built-in `Clone` impls of tuples
(<https://doc.rust-lang.org/std/primitive.tuple.html#impl-Clone-for-(T,)>): the components are
cloned in order. Note that Aeneas translates the 1-tuple `(A,)` to `A`.

We disable `linter.checkUnivs` because the components of a tuple may live in different universes. -/

@[expose, rust_fun "core::clone::{core::clone::Clone<()>}::clone"]
def core.clone.CloneUnit.clone (x : Unit) : Result Unit := .ok x

@[expose, reducible, rust_trait_impl "core::clone::Clone<()>"]
def core.clone.CloneUnit : core.clone.Clone Unit := {
  clone := core.clone.CloneUnit.clone
}

@[expose, rust_fun "core::clone::{core::clone::Clone<(@A)>}::clone"]
def core.clone.CloneTuple1.clone {A : Type _}
  (CloneInstA : core.clone.Clone A)
  (x : A) : Result A :=
  CloneInstA.clone x

@[expose, reducible, rust_trait_impl "core::clone::Clone<(@A)>"]
def core.clone.CloneTuple1 {A : Type _}
  (CloneInstA : core.clone.Clone A) :
  core.clone.Clone A := {
  clone := core.clone.CloneTuple1.clone CloneInstA
}

set_option linter.checkUnivs false in
@[expose, rust_fun "core::clone::{core::clone::Clone<(@A, @B)>}::clone"]
def core.clone.CloneTuple2.clone {A B : Type _}
  (CloneInstA : core.clone.Clone A) (CloneInstB : core.clone.Clone B)
  (x : A × B) : Result (A × B) := do
  let (a, b) := x
  let a' ← CloneInstA.clone a
  let b' ← CloneInstB.clone b
  .ok (a', b')

set_option linter.checkUnivs false in
@[expose, reducible, rust_trait_impl "core::clone::Clone<(@A, @B)>"]
def core.clone.CloneTuple2 {A B : Type _}
  (CloneInstA : core.clone.Clone A) (CloneInstB : core.clone.Clone B) :
  core.clone.Clone (A × B) := {
  clone := core.clone.CloneTuple2.clone CloneInstA CloneInstB
}

set_option linter.checkUnivs false in
@[expose, rust_fun "core::clone::{core::clone::Clone<(@A, @B, @C)>}::clone"]
def core.clone.CloneTuple3.clone {A B C : Type _}
  (CloneInstA : core.clone.Clone A)
  (CloneInstB : core.clone.Clone B)
  (CloneInstC : core.clone.Clone C)
  (x : A × B × C) : Result (A × B × C) := do
  let (a, b, c) := x
  let a' ← CloneInstA.clone a
  let b' ← CloneInstB.clone b
  let c' ← CloneInstC.clone c
  .ok (a', b', c')

set_option linter.checkUnivs false in
@[expose, reducible, rust_trait_impl "core::clone::Clone<(@A, @B, @C)>"]
def core.clone.CloneTuple3 {A B C : Type _}
  (CloneInstA : core.clone.Clone A)
  (CloneInstB : core.clone.Clone B)
  (CloneInstC : core.clone.Clone C) :
  core.clone.Clone (A × B × C) := {
  clone := core.clone.CloneTuple3.clone CloneInstA CloneInstB CloneInstC
}

set_option linter.checkUnivs false in
@[expose, rust_fun "core::clone::{core::clone::Clone<(@A, @B, @C, @D)>}::clone"]
def core.clone.CloneTuple4.clone {A B C D : Type _}
  (CloneInstA : core.clone.Clone A)
  (CloneInstB : core.clone.Clone B)
  (CloneInstC : core.clone.Clone C)
  (CloneInstD : core.clone.Clone D)
  (x : A × B × C × D) : Result (A × B × C × D) := do
  let (a, b, c, d) := x
  let a' ← CloneInstA.clone a
  let b' ← CloneInstB.clone b
  let c' ← CloneInstC.clone c
  let d' ← CloneInstD.clone d
  .ok (a', b', c', d')

set_option linter.checkUnivs false in
@[expose, reducible, rust_trait_impl "core::clone::Clone<(@A, @B, @C, @D)>"]
def core.clone.CloneTuple4 {A B C D : Type _}
  (CloneInstA : core.clone.Clone A)
  (CloneInstB : core.clone.Clone B)
  (CloneInstC : core.clone.Clone C)
  (CloneInstD : core.clone.Clone D) :
  core.clone.Clone (A × B × C × D) := {
  clone := core.clone.CloneTuple4.clone CloneInstA CloneInstB CloneInstC CloneInstD
}

set_option linter.checkUnivs false in
@[expose, rust_fun "core::clone::{core::clone::Clone<(@A, @B, @C, @D, @E)>}::clone"]
def core.clone.CloneTuple5.clone {A B C D E : Type _}
  (CloneInstA : core.clone.Clone A)
  (CloneInstB : core.clone.Clone B)
  (CloneInstC : core.clone.Clone C)
  (CloneInstD : core.clone.Clone D)
  (CloneInstE : core.clone.Clone E)
  (x : A × B × C × D × E) : Result (A × B × C × D × E) := do
  let (a, b, c, d, e) := x
  let a' ← CloneInstA.clone a
  let b' ← CloneInstB.clone b
  let c' ← CloneInstC.clone c
  let d' ← CloneInstD.clone d
  let e' ← CloneInstE.clone e
  .ok (a', b', c', d', e')

set_option linter.checkUnivs false in
@[expose, reducible, rust_trait_impl "core::clone::Clone<(@A, @B, @C, @D, @E)>"]
def core.clone.CloneTuple5 {A B C D E : Type _}
  (CloneInstA : core.clone.Clone A)
  (CloneInstB : core.clone.Clone B)
  (CloneInstC : core.clone.Clone C)
  (CloneInstD : core.clone.Clone D)
  (CloneInstE : core.clone.Clone E) :
  core.clone.Clone (A × B × C × D × E) := {
  clone := core.clone.CloneTuple5.clone CloneInstA CloneInstB CloneInstC CloneInstD CloneInstE
}

set_option linter.checkUnivs false in
@[expose, rust_fun "core::clone::{core::clone::Clone<(@A, @B, @C, @D, @E, @F)>}::clone"]
def core.clone.CloneTuple6.clone {A B C D E F : Type _}
  (CloneInstA : core.clone.Clone A)
  (CloneInstB : core.clone.Clone B)
  (CloneInstC : core.clone.Clone C)
  (CloneInstD : core.clone.Clone D)
  (CloneInstE : core.clone.Clone E)
  (CloneInstF : core.clone.Clone F)
  (x : A × B × C × D × E × F) : Result (A × B × C × D × E × F) := do
  let (a, b, c, d, e, f) := x
  let a' ← CloneInstA.clone a
  let b' ← CloneInstB.clone b
  let c' ← CloneInstC.clone c
  let d' ← CloneInstD.clone d
  let e' ← CloneInstE.clone e
  let f' ← CloneInstF.clone f
  .ok (a', b', c', d', e', f')

set_option linter.checkUnivs false in
@[expose, reducible, rust_trait_impl "core::clone::Clone<(@A, @B, @C, @D, @E, @F)>"]
def core.clone.CloneTuple6 {A B C D E F : Type _}
  (CloneInstA : core.clone.Clone A)
  (CloneInstB : core.clone.Clone B)
  (CloneInstC : core.clone.Clone C)
  (CloneInstD : core.clone.Clone D)
  (CloneInstE : core.clone.Clone E)
  (CloneInstF : core.clone.Clone F) :
  core.clone.Clone (A × B × C × D × E × F) := {
  clone :=
    core.clone.CloneTuple6.clone CloneInstA CloneInstB CloneInstC CloneInstD CloneInstE CloneInstF
}

end Std

end Aeneas
