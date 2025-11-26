import Lean
import Aeneas.Std.Primitives
import Aeneas.Progress.Init

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

/- [core::clone::impls::{(core::clone::Clone for bool)#19}::clone] -/
@[reducible, simp, progress_simps]
def clone.impls.CloneBool.clone (b : Bool) : Bool := b

@[reducible, rust_trait_impl "core::clone::Clone<bool>"]
def clone.CloneBool : clone.Clone Bool := {
  clone := fun b => ok (clone.impls.CloneBool.clone b)
  clone_from := fun _ b => ok (clone.impls.CloneBool.clone b)
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

@[rust_trait "core::cmp::PartialEq"]
structure core.cmp.PartialEq (Self : Type) (Rhs : Type) where
  eq : Self → Rhs → Result Bool
  ne : Self → Rhs → Result Bool := fun self other => do not (← eq self other)

/- Trait declaration: [core::cmp::Eq]
   Name pattern: core::cmp::Eq -/
@[rust_trait "core::cmp::Eq" (parentClauses := ["partialEqInst"])]
structure core.cmp.Eq (Self : Type) where
  partialEqInst : core.cmp.PartialEq Self Self

/- Default method -/
@[rust_fun "core::cmp::PartialEq::ne"]
def core.cmp.PartialEq.ne.default {Self Rhs : Type} (eq : Self → Rhs → Result Bool)
  (self : Self) (other : Rhs) : Result Bool := do
  ok (¬ (← eq self other))

/- We model the Rust ordering with the native Lean ordering -/
attribute
  [rust_type "core::cmp::Ordering"
  (body := .enum [⟨"Less", "lt", none⟩, ⟨"Equal", "eq", none⟩, ⟨"Greater", "gt", none⟩])]
  Ordering

@[rust_trait "core::cmp::PartialOrd" (parentClauses := ["partialEqInst"])]
structure core.cmp.PartialOrd (Self : Type) (Rhs : Type) where
  partialEqInst : core.cmp.PartialEq Self Rhs
  partial_cmp : Self → Rhs → Result (Option Ordering)
  lt : Self → Rhs → Result Bool
  le : Self → Rhs → Result Bool
  gt : Self → Rhs → Result Bool
  ge : Self → Rhs → Result Bool

/- Default method -/
@[rust_fun "core::cmp::PartialOrd::lt"]
def core.cmp.PartialOrd.lt.default {Self Rhs : Type}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .lt)

/- Default method -/
@[rust_fun "core::cmp::PartialOrd::le"]
def core.cmp.PartialOrd.le.default {Self Rhs : Type}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .lt ∨ cmp = some .eq)

/- Default method -/
@[rust_fun "core::cmp::PartialOrd::gt"]
def core.cmp.PartialOrd.gt.default {Self Rhs : Type}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .gt)

/- Default method -/
@[rust_fun "core::cmp::PartialOrd::ge"]
def core.cmp.PartialOrd.ge.default {Self Rhs : Type}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .gt ∨ cmp = some .eq)

@[rust_trait "core::cmp::Ord" (parentClauses := ["eqInst", "partialOrdInst"])]
structure core.cmp.Ord (Self : Type) where
  eqInst : core.cmp.Eq Self
  partialOrdInst : core.cmp.PartialOrd Self Self
  cmp : Self → Self → Result Ordering
  max : Self → Self → Result Self
  min : Self → Self → Result Self
  clamp : Self → Self → Self → Result Self

/- Default method -/
@[rust_fun "core::cmp::Ord::max"]
def core.cmp.Ord.max.default {Self : Type} (lt : Self → Self → Result Bool)
  (x y : Self) : Result Self := do
  if ← lt x y then ok y else ok x

/- Default method -/
@[rust_fun "core::cmp::Ord::min"]
def core.cmp.Ord.min.default {Self : Type} (lt : Self → Self → Result Bool)
  (x y : Self) : Result Self := do
  if ← lt x y then ok x else ok y

/- Default method -/
@[rust_fun "core::cmp::Ord::clamp"]
def core.cmp.Ord.clamp.default {Self : Type} (le lt gt : Self → Self → Result Bool)
  (self min max : Self) : Result Self := do
  massert (← le min max)
  if ← lt self min then ok min
  else if ← gt self max then ok max
  else ok self

@[simp, rust_fun "core::cmp::min"]
def core.cmp.min {T : Type} (OrdInst : core.cmp.Ord T) (x y : T) : Result T :=
  -- TODO: is this the correct model?
  OrdInst.min x y

@[simp, rust_fun "core::cmp::max"]
def core.cmp.max {T : Type} (OrdInst : core.cmp.Ord T) (x y : T) : Result T :=
  -- TODO: is this the correct model?
  OrdInst.max x y

@[simp, rust_fun "core::cmp::impls::{core::cmp::PartialEq<(), ()>}::eq"]
def core.cmp.impls.PartialEqUnit.eq (_ _ : Unit) : Result Bool := ok true

@[simp, rust_fun "core::cmp::impls::{core::cmp::PartialEq<(), ()>}::ne"]
def core.cmp.impls.PartialEqUnit.ne (_ _ : Unit) : Result Bool := ok false

@[simp, rust_fun "core::cmp::impls::{core::cmp::PartialOrd<(), ()>}::partial_cmp"]
def core.cmp.impls.PartialOrdUnit.partial_cmp (_ _ : Unit) : Result (Option Ordering) :=
  ok (some .eq)

@[simp, rust_fun "core::cmp::impls::{core::cmp::Ord<()>}::cmp"]
def core.cmp.impls.OrdUnit.cmp (_ _ : Unit) : Result Ordering :=
  ok .eq

@[rust_type "core::panicking::AssertKind"]
inductive core.panicking.AssertKind where
| Eq : core.panicking.AssertKind
| Ne : core.panicking.AssertKind
| Match : core.panicking.AssertKind

@[rust_fun "core::clone::impls::{core::clone::Clone<&'0 @T>}::clone"]
def core.clone.impls.CloneShared.clone {T : Type} (x : T) : Result T := .ok x

end Std

end Aeneas
