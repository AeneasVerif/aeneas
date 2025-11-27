import Aeneas.Extract
import Aeneas.Std.Primitives

namespace Aeneas.Std

open Result

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

@[reducible, rust_trait_impl "core::cmp::PartialEq<(), ()>"]
def core.cmp.PartialEqUnit : core.cmp.PartialEq Unit Unit := {
  eq := core.cmp.impls.PartialEqUnit.eq
  ne := core.cmp.impls.PartialEqUnit.ne
}

@[simp, rust_fun "core::cmp::impls::{core::cmp::PartialOrd<(), ()>}::partial_cmp"]
def core.cmp.impls.PartialOrdUnit.partial_cmp (_ _ : Unit) : Result (Option Ordering) :=
  ok (some .eq)

@[simp, rust_fun "core::cmp::impls::{core::cmp::Ord<()>}::cmp"]
def core.cmp.impls.OrdUnit.cmp (_ _ : Unit) : Result Ordering :=
  ok .eq

end Aeneas.Std
