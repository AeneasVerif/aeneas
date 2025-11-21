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

namespace ops -- core.ops

namespace index -- core.ops.index

@[rust_trait "core::ops::index::Index"]
structure Index (Self Idx Output : Type) where
  index : Self → Idx → Result Output

@[rust_trait "core::ops::index::IndexMut" (parentClauses := ["indexInst"])]
structure IndexMut (Self Idx Output : Type) where
  indexInst : Index Self Idx Output
  index_mut : Self → Idx → Result (Output × (Output → Self))

end index -- core.ops.index

namespace deref -- core.ops.deref

@[rust_trait "core::ops::deref::Deref"]
structure Deref (Self Target : Type) where
  deref : Self → Result Target

@[rust_trait "core::ops::deref::DerefMut" (parentClauses := ["derefInst"])]
structure DerefMut (Self Target : Type) where
  derefInst : Deref Self Target
  deref_mut : Self → Result (Target × (Target → Self))

end deref -- core.ops.deref

end ops -- core.ops

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

@[rust_trait "core::convert::Into"]
structure core.convert.Into (Self : Type) (T : Type) where
  into : Self → Result T

@[reducible, simp, progress_simps, rust_fun "core::convert::{core::convert::Into<@T, @U>}::into"]
def core.convert.IntoFrom.into {T : Type} {U : Type}
  (fromInst : core.convert.From U T) (x : T) : Result U :=
  fromInst.from_ x

@[reducible, rust_trait_impl "core::convert::Into<@Self, @T>"]
def core.convert.IntoFrom {T : Type} {U : Type} (fromInst : core.convert.From U T)
  : core.convert.Into T U := {
  into := core.convert.IntoFrom.into fromInst
}

@[simp, progress_simps, rust_fun "core::convert::{core::convert::From<@T, @T>}::from" -canFail]
def core.convert.FromSame.from_ {T : Type} (x : T) : T := x

@[reducible, rust_trait_impl "core::convert::From<@Self, @Self>"]
def core.convert.FromSame (T : Type) : core.convert.From T T := {
  from_ := fun x => ok (core.convert.FromSame.from_ x)
}

@[rust_type "core::result::Result"]
inductive core.result.Result (T : Type) (E : Type) where
| Ok : T → core.result.Result T E
| Err : E → core.result.Result T E

@[reducible, rust_type "core::fmt::Error"]
def core.fmt.Error := Unit

@[rust_trait "core::convert::TryFrom"]
structure core.convert.TryFrom (Self T Error : Type) where
  try_from : T → Result (core.result.Result Self Error)

@[rust_trait "core::convert::TryInto"]
structure core.convert.TryInto (Self T Error : Type) where
  try_into : Self → Result (core.result.Result T Error)

@[reducible, simp]
def core.convert.TryIntoFrom.try_into {T U Error : Type} (fromInst : core.convert.TryFrom U T Error)
  (x : T) : Result (core.result.Result U Error) :=
  fromInst.try_from x

@[reducible, rust_trait_impl "core::convert::{core::convert::TryInto<@T, @U>}"]
def core.convert.TryIntoFrom {T U Error : Type} (fromInst : core.convert.TryFrom U T Error) :
  core.convert.TryInto T U Error := {
  try_into := core.convert.TryIntoFrom.try_into fromInst
}

@[rust_trait "core::convert::AsMut"]
structure core.convert.AsMut (Self : Type) (T : Type) where
  as_mut : Self → Result (T × (T → Self))

@[reducible, rust_trait_impl "core::convert::AsMut<Box<@T>, @T>"]
def core.convert.AsMutBox (T : Type) : core.convert.AsMut T T := {
  as_mut := fun x => ok (alloc.boxed.AsMutBox.as_mut x)
}

/- TODO: -/
@[rust_type "core::fmt::Formatter"]
axiom Formatter : Type

@[rust_trait "core::fmt::Debug"]
structure core.fmt.Debug (T : Type) where
  fmt : T → Formatter → Result (Formatter × Formatter → Formatter)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap"]
def core.result.Result.unwrap {T E : Type}
  (_ : core.fmt.Debug T) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => ok x
  | .Err _ => fail .panic

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

end Std

end Aeneas
