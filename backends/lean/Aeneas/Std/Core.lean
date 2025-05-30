import Lean
import Aeneas.Std.Primitives
import Aeneas.Progress.Init

namespace Aeneas

namespace Std

open Result

/- [alloc::boxed::{core::convert::AsMut<T> for alloc::boxed::Box<T>}::as_mut] -/
def alloc.boxed.AsMutBoxT.as_mut {T : Type} (x : T) : T × (T → T) :=
  (x, fun x => x)

namespace core

/- Trait declaration: [core::convert::From] -/
structure convert.From (Self T : Type) where
  from_ : T → Result Self

namespace ops -- core.ops

namespace index -- core.ops.index

/- Trait declaration: [core::ops::index::Index] -/
structure Index (Self Idx Output : Type) where
  index : Self → Idx → Result Output

/- Trait declaration: [core::ops::index::IndexMut] -/
structure IndexMut (Self Idx Output : Type) where
  indexInst : Index Self Idx Output
  index_mut : Self → Idx → Result (Output × (Output → Self))

end index -- core.ops.index

namespace deref -- core.ops.deref

structure Deref (Self Target : Type) where
  deref : Self → Result Target

structure DerefMut (Self Target : Type) where
  derefInst : Deref Self Target
  deref_mut : Self → Result (Target × (Target → Self))

end deref -- core.ops.deref

end ops -- core.ops

/- Trait declaration: [core::clone::Clone] -/
structure clone.Clone (Self : Type) where
  clone : Self → Result Self
  clone_from : Self → Self → Result Self := fun _ => clone


def clone.Clone.from_from.default {Self : Type} (clone : Self → Result Self)
  (_self source : Self) : Result Self :=
  clone source

/- [core::clone::impls::{(core::clone::Clone for bool)#19}::clone] -/
@[reducible, simp, progress_simps]
def clone.impls.CloneBool.clone (b : Bool) : Bool := b

@[reducible]
def clone.CloneBool : clone.Clone Bool := {
  clone := fun b => ok (clone.impls.CloneBool.clone b)
  clone_from := fun _ b => ok (clone.impls.CloneBool.clone b)
}

/- [core::marker::Copy] -/
structure marker.Copy (Self : Type) where
  cloneInst : core.clone.Clone Self

/- [core::mem::replace]

   This acts like a swap effectively in a functional pure world.
   We return the old value of `dst`, i.e. `dst` itself.
   The new value of `dst` is `src`. -/
@[simp, progress_simps] def mem.replace {a : Type} (dst : a) (src : a) : a × a := (dst, src)

/- [core::mem::swap] -/
@[simp, progress_simps] def mem.swap {T : Type} (a b : T): T × T := (b, a)

end core

/- [core::option::{core::option::Option<T>}::unwrap] -/
@[simp, progress_simps] def core.option.Option.unwrap {T : Type} (x : Option T) : Result T :=
  Result.ofOption x Error.panic

/- [core::option::{core::option::Option<T>}::unwrap_or] -/
@[progress_pure_def]
def core.option.Option.unwrap_or (self : Option T) (default : T) : T :=
  match self with
  | none => default
  | some self => self

@[simp] def core.option.Option.unwrap_or_some (self default : T) :
  core.option.Option.unwrap_or (some self) default = self := by simp [unwrap_or]

@[simp] def core.option.Option.unwrap_or_none (default : T) :
  core.option.Option.unwrap_or none default = default := by simp [unwrap_or]

/- [core::option::Option::take] -/
@[simp, progress_simps] def core.option.Option.take {T: Type} (self: Option T): Option T × Option T := (self, .none)

/- [core::option::Option::is_none] -/
@[simp, progress_simps] def core.option.Option.is_none {T: Type} (self: Option T): Bool := self.isNone

/- [core::convert::Into] -/
structure core.convert.Into (Self : Type) (T : Type) where
  into : Self → Result T

/- [core::convert::{core::convert::Into<U> for T}::into] -/
@[reducible, simp, progress_simps]
def core.convert.IntoFrom.into {T : Type} {U : Type}
  (fromInst : core.convert.From U T) (x : T) : Result U :=
  fromInst.from_ x

/- Trait implementation: [core::convert::{core::convert::Into<U> for T}] -/
@[reducible]
def core.convert.IntoFrom {T : Type} {U : Type} (fromInst : core.convert.From U T)
  : core.convert.Into T U := {
  into := core.convert.IntoFrom.into fromInst
}

/- [core::convert::{core::convert::From<T> for T}::from] -/
@[simp, progress_simps] def core.convert.FromSame.from_ {T : Type} (x : T) : T := x

/- [core::convert::{core::convert::From<T> for T}] -/
@[reducible]
def core.convert.FromSame (T : Type) : core.convert.From T T := {
  from_ := fun x => ok (core.convert.FromSame.from_ x)
}

/- [core::result::Result] -/
inductive core.result.Result (T : Type) (E : Type) where
| Ok : T → core.result.Result T E
| Err : E → core.result.Result T E

/- [core::fmt::Error] -/
@[reducible] def core.fmt.Error := Unit

structure core.convert.TryFrom (Self T : Type) where
  Error : Type
  try_from : T → Result (core.result.Result Self Error)

structure core.convert.TryInto (Self T : Type) where
  Error : Type
  try_into : Self → Result (core.result.Result T Error)

@[reducible, simp]
def core.convert.TryIntoFrom.try_into {T U : Type} (fromInst : core.convert.TryFrom U T)
  (x : T) : Result (core.result.Result U fromInst.Error) :=
  fromInst.try_from x

@[reducible]
def core.convert.TryIntoFrom {T U : Type} (fromInst : core.convert.TryFrom U T) :
  core.convert.TryInto T U := {
  Error := fromInst.Error
  try_into := core.convert.TryIntoFrom.try_into fromInst
}

structure core.convert.AsMut (Self : Type) (T : Type) where
  as_mut : Self → Result (T × (T → Self))

/- [alloc::boxed::{core::convert::AsMut<T> for alloc::boxed::Box<T>}] -/
@[reducible]
def core.convert.AsMutBoxT (T : Type) : core.convert.AsMut T T := {
  as_mut := fun x => ok (alloc.boxed.AsMutBoxT.as_mut x)
}

/- TODO: -/
axiom Formatter : Type

structure core.fmt.Debug (T : Type) where
  fmt : T → Formatter → Result (Formatter × Formatter → Formatter)

def core.result.Result.unwrap {T E : Type}
  (_ : core.fmt.Debug T) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => ok x
  | .Err _ => fail .panic

/- [core::ops::range::RangeFrom] -/
structure core.ops.range.RangeFrom (Idx : Type) where
  start : Idx

/- Trait declaration: [core::cmp::PartialEq]
   Name pattern: core::cmp::PartialEq -/
structure core.cmp.PartialEq (Self : Type) (Rhs : Type) where
  eq : Self → Rhs → Result Bool
  ne : Self → Rhs → Result Bool := fun self other => do not (← eq self other)

/- Trait declaration: [core::cmp::Eq]
   Name pattern: core::cmp::Eq -/
structure core.cmp.Eq (Self : Type) where
  partialEqInst : core.cmp.PartialEq Self Self

/- Default method
   Name pattern: core::cmp::PartialEq::ne
-/
def core.cmp.PartialEq.ne.default {Self Rhs : Type} (eq : Self → Rhs → Result Bool)
  (self : Self) (other : Rhs) : Result Bool := do
  ok (¬ (← eq self other))

/- Trait declaration: [core::cmp::PartialOrd]
   Name pattern: core::cmp::PartialOrd -/
structure core.cmp.PartialOrd (Self : Type) (Rhs : Type) where
  partialEqInst : core.cmp.PartialEq Self Rhs
  partial_cmp : Self → Rhs → Result (Option Ordering)
  lt : Self → Rhs → Result Bool
  le : Self → Rhs → Result Bool
  gt : Self → Rhs → Result Bool
  ge : Self → Rhs → Result Bool

/- Default method
   Name pattern: core::cmp::PartialOrd::lt -/
def core.cmp.PartialOrd.lt.default {Self Rhs : Type}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .lt)

/- Default method
   Name pattern: core::cmp::PartialOrd::le -/
def core.cmp.PartialOrd.le.default {Self Rhs : Type}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .lt ∨ cmp = some .eq)

/- Default method
   Name pattern: core::cmp::PartialOrd::gt -/
def core.cmp.PartialOrd.gt.default {Self Rhs : Type}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .gt)

/- Default method
   Name pattern: core::cmp::PartialOrd::ge -/
def core.cmp.PartialOrd.ge.default {Self Rhs : Type}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .gt ∨ cmp = some .eq)

/- Trait declaration: [core::cmp::Ord]
   Name pattern: core::cmp::Ord -/
structure core.cmp.Ord (Self : Type) where
  eqInst : core.cmp.Eq Self
  partialOrdInst : core.cmp.PartialOrd Self Self
  cmp : Self → Self → Result Ordering
  max : Self → Self → Result Self
  min : Self → Self → Result Self
  clamp : Self → Self → Self → Result Self

/- Default method for: [core::cmp::Ord::max]:
   Name pattern: core::cmp::Ord::max -/
def core.cmp.Ord.max.default {Self : Type} (lt : Self → Self → Result Bool)
  (x y : Self) : Result Self := do
  if ← lt x y then ok y else ok x

/- Default method for: [core::cmp::Ord::min]:
   Name pattern: core::cmp::Ord::min -/
def core.cmp.Ord.min.default {Self : Type} (lt : Self → Self → Result Bool)
  (x y : Self) : Result Self := do
  if ← lt x y then ok x else ok y

/- Default method for: [core::cmp::Ord::clamp]:
   Name pattern: core::cmp::Ord::clamp -/
def core.cmp.Ord.min.clamp {Self : Type} (le lt gt : Self → Self → Result Bool)
  (self min max : Self) : Result Self := do
  massert (← le min max)
  if ← lt self min then ok min
  else if ← gt self max then ok max
  else ok self

end Std

end Aeneas
