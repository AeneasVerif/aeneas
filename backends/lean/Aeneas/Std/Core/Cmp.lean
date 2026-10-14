module
public import Aeneas.Extract
public import Aeneas.Std.Primitives
public import Aeneas.Std.WP
public import Aeneas.Tactic.Step.Init
public import Aeneas.Tactic.Elab.TraitDefault.Init
public section

namespace Aeneas.Std

open Result

@[rust_trait "core::cmp::PartialEq"]
structure core.cmp.PartialEq (Self : Type _) (Rhs : Type _) where
  eq : Self → Rhs → Result Bool
  ne : Self → Rhs → Result Bool := fun self other => do ok (not (← eq self other))

@[rust_trait "core::cmp::Eq" (parentClauses := ["partialEqInst"])]
structure core.cmp.Eq (Self : Type _) where
  partialEqInst : core.cmp.PartialEq Self Self
  assert_fields_are_eq (_ : Self) : Result Unit := .ok ()

@[expose, simp, trait_default, rust_fun "core::cmp::Eq::assert_fields_are_eq"]
def core.cmp.Eq.assert_fields_are_eq.default
  {Self : Type _} (_EqInst : core.cmp.Eq Self) (_x : Self) : Result Unit :=
  .ok ()

/- Default method. -/
def core.cmp.PartialEq.ne.default {Self Rhs : Type _} (eq : Self → Rhs → Result Bool)
  (self : Self) (other : Rhs) : Result Bool := do
  ok (¬ (← eq self other))

@[expose, trait_default, rust_fun "core::cmp::PartialEq::ne"]
def core.cmp.PartialEq.ne.trait_default {Self Rhs : Type _}
  (PartialEqInst : core.cmp.PartialEq Self Rhs)
  (self : Self) (other : Rhs) : Result Bool :=
  core.cmp.PartialEq.ne.default PartialEqInst.eq self other

/-- Step spec for the homogeneous `PartialEq::ne`. -/
@[step]
theorem core.cmp.PartialEq.ne.default.spec {T : Type _}
  (eq : T → T → Result Bool) (self : T) (other : T)
  (hEq : eq self other ⦃ b => b ↔ (self = other) ⦄) :
  core.cmp.PartialEq.ne.default eq self other ⦃ b => b ↔ (self ≠ other) ⦄ := by
  unfold core.cmp.PartialEq.ne.default
  apply WP.spec_bind hEq
  intro b hb
  simp only [WP.spec_ok]
  cases b <;> simp_all

/-- Step spec for the homogeneous `PartialEq::ne`. -/
@[step]
theorem core.cmp.PartialEq.ne.trait_default.spec {T : Type _}
  (PartialEqInst : core.cmp.PartialEq T T) (self : T) (other : T)
  (hEq : PartialEqInst.eq self other ⦃ b => b ↔ (self = other) ⦄) :
  core.cmp.PartialEq.ne.trait_default PartialEqInst self other ⦃ b => b ↔ (self ≠ other) ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default
  exact core.cmp.PartialEq.ne.default.spec PartialEqInst.eq self other hEq

/- We model the Rust ordering with the native Lean ordering -/
attribute
  [rust_type "core::cmp::Ordering"
  (body := .enum [⟨"Less", "lt", none⟩, ⟨"Equal", "eq", none⟩, ⟨"Greater", "gt", none⟩])]
  Ordering

/- Auxiliary functions for the default implementations of `PartialOrd` methods -/
@[expose] def core.cmp.PartialOrd.lt_body {Self Rhs : Type _}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .lt)

@[expose] def core.cmp.PartialOrd.le_body {Self Rhs : Type _}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .lt ∨ cmp = some .eq)

@[expose] def core.cmp.PartialOrd.gt_body {Self Rhs : Type _}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .gt)

@[expose] def core.cmp.PartialOrd.ge_body {Self Rhs : Type _}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool := do
  let cmp ← partial_cmp x y
  ok (cmp = some .gt ∨ cmp = some .eq)

@[rust_trait "core::cmp::PartialOrd" (parentClauses := ["partialEqInst"])]
structure core.cmp.PartialOrd (Self : Type _) (Rhs : Type _) where
  partialEqInst : core.cmp.PartialEq Self Rhs
  partial_cmp : Self → Rhs → Result (Option Ordering)
  lt : Self → Rhs → Result Bool := core.cmp.PartialOrd.lt_body partial_cmp
  le : Self → Rhs → Result Bool := core.cmp.PartialOrd.le_body partial_cmp
  gt : Self → Rhs → Result Bool := core.cmp.PartialOrd.gt_body partial_cmp
  ge : Self → Rhs → Result Bool := core.cmp.PartialOrd.ge_body partial_cmp

/- Default method -/
@[expose] def core.cmp.PartialOrd.lt.default {Self Rhs : Type _}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool :=
  core.cmp.PartialOrd.lt_body partial_cmp x y

@[expose, trait_default, rust_fun "core::cmp::PartialOrd::lt"]
def core.cmp.PartialOrd.lt.trait_default {Self Rhs : Type _}
  (PartialOrdInst : core.cmp.PartialOrd Self Rhs)
  (x : Self) (y : Rhs) : Result Bool :=
  core.cmp.PartialOrd.lt.default PartialOrdInst.partial_cmp x y

/- Default method -/
@[expose] def core.cmp.PartialOrd.le.default {Self Rhs : Type _}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool :=
  core.cmp.PartialOrd.le_body partial_cmp x y

@[expose, trait_default, rust_fun "core::cmp::PartialOrd::le"]
def core.cmp.PartialOrd.le.trait_default {Self Rhs : Type _}
  (PartialOrdInst : core.cmp.PartialOrd Self Rhs)
  (x : Self) (y : Rhs) : Result Bool :=
  core.cmp.PartialOrd.le.default PartialOrdInst.partial_cmp x y

/- Default method -/
@[expose] def core.cmp.PartialOrd.gt.default {Self Rhs : Type _}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool :=
  core.cmp.PartialOrd.gt_body partial_cmp x y

@[expose, trait_default, rust_fun "core::cmp::PartialOrd::gt"]
def core.cmp.PartialOrd.gt.trait_default {Self Rhs : Type _}
  (PartialOrdInst : core.cmp.PartialOrd Self Rhs)
  (x : Self) (y : Rhs) : Result Bool :=
  core.cmp.PartialOrd.gt.default PartialOrdInst.partial_cmp x y

/- Default method -/
@[expose] def core.cmp.PartialOrd.ge.default {Self Rhs : Type _}
  (partial_cmp : Self → Rhs → Result (Option Ordering))
  (x : Self) (y : Rhs) : Result Bool :=
  core.cmp.PartialOrd.ge_body partial_cmp x y

@[expose, trait_default, rust_fun "core::cmp::PartialOrd::ge"]
def core.cmp.PartialOrd.ge.trait_default {Self Rhs : Type _}
  (PartialOrdInst : core.cmp.PartialOrd Self Rhs)
  (x : Self) (y : Rhs) : Result Bool :=
  core.cmp.PartialOrd.ge.default PartialOrdInst.partial_cmp x y

/- Auxiliary functions for the default implementations of `Ord` methods.
   They use `Std.bind` rather than `do`: Lean's `do` would force `Self : Type` (it binds `Bool`s
   and returns a `Self` in the same block). -/
@[expose] def core.cmp.Ord.max_body {Self : Type _} (lt : Self → Self → Result Bool)
  (x y : Self) : Result Self :=
  bind (lt y x) fun b => if b then ok x else ok y

@[expose] def core.cmp.Ord.min_body {Self : Type _} (lt : Self → Self → Result Bool)
  (x y : Self) : Result Self :=
  bind (lt y x) fun b => if b then ok y else ok x

@[expose] def core.cmp.Ord.clamp_body {Self : Type _} (le lt gt : Self → Self → Result Bool)
  (self min max : Self) : Result Self :=
  bind (le min max) fun b => bind (massert b) fun _ =>
  bind (lt self min) fun b => if b then ok min else
  bind (gt self max) fun b => if b then ok max else ok self

@[rust_trait "core::cmp::Ord" (parentClauses := ["eqInst", "partialOrdInst"])]
structure core.cmp.Ord (Self : Type _) where
  eqInst : core.cmp.Eq Self
  partialOrdInst : core.cmp.PartialOrd Self Self
  cmp : Self → Self → Result Ordering
  max : Self → Self → Result Self :=
    core.cmp.Ord.max_body partialOrdInst.lt
  min : Self → Self → Result Self :=
    core.cmp.Ord.min_body partialOrdInst.lt
  clamp : Self → Self → Self → Result Self :=
    core.cmp.Ord.clamp_body partialOrdInst.le partialOrdInst.lt partialOrdInst.gt

/- Default method -/
@[expose] def core.cmp.Ord.max.default {Self : Type _} (lt : Self → Self → Result Bool)
  (x y : Self) : Result Self :=
  core.cmp.Ord.max_body lt x y

@[expose, trait_default, rust_fun "core::cmp::Ord::max"]
def core.cmp.Ord.max.trait_default {Self : Type _} (OrdInst : core.cmp.Ord Self)
  (x y : Self) : Result Self :=
  core.cmp.Ord.max.default OrdInst.partialOrdInst.lt x y

@[expose] def core.cmp.Ord.min.default {Self : Type _} (lt : Self → Self → Result Bool)
  (x y : Self) : Result Self :=
  core.cmp.Ord.min_body lt x y

@[expose, trait_default, rust_fun "core::cmp::Ord::min"]
def core.cmp.Ord.min.trait_default {Self : Type _} (OrdInst : core.cmp.Ord Self)
  (x y : Self) : Result Self :=
  core.cmp.Ord.min.default OrdInst.partialOrdInst.lt x y

/- Default method -/
@[expose] def core.cmp.Ord.clamp.default {Self : Type _} (le lt gt : Self → Self → Result Bool)
  (self min max : Self) : Result Self :=
  core.cmp.Ord.clamp_body le lt gt self min max

@[expose, trait_default, rust_fun "core::cmp::Ord::clamp"]
def core.cmp.Ord.clamp.trait_default {Self : Type _} (OrdInst : core.cmp.Ord Self)
  (self min max : Self) : Result Self :=
  core.cmp.Ord.clamp.default OrdInst.partialOrdInst.le OrdInst.partialOrdInst.lt
    OrdInst.partialOrdInst.gt self min max

@[expose, simp, rust_fun "core::cmp::min"]
def core.cmp.min {T : Type _} (OrdInst : core.cmp.Ord T) (x y : T) : Result T :=
  -- TODO: is this the correct model?
  OrdInst.min x y

@[expose, simp, rust_fun "core::cmp::max"]
def core.cmp.max {T : Type _} (OrdInst : core.cmp.Ord T) (x y : T) : Result T :=
  -- TODO: is this the correct model?
  OrdInst.max x y

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialEq<(), ()>}::eq"]
def core.cmp.impls.PartialEqUnit.eq (_ _ : Unit) : Result Bool := ok true

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialEq<(), ()>}::ne"]
def core.cmp.impls.PartialEqUnit.ne (_ _ : Unit) : Result Bool := ok false

@[expose, reducible, rust_trait_impl "core::cmp::PartialEq<(), ()>"]
def core.cmp.PartialEqUnit : core.cmp.PartialEq Unit Unit := {
  eq := core.cmp.impls.PartialEqUnit.eq
  ne := core.cmp.impls.PartialEqUnit.ne
}

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialOrd<(), ()>}::partial_cmp"]
def core.cmp.impls.PartialOrdUnit.partial_cmp (_ _ : Unit) : Result (Option Ordering) :=
  ok (some .eq)

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::Ord<()>}::cmp"]
def core.cmp.impls.OrdUnit.cmp (_ _ : Unit) : Result Ordering :=
  ok .eq

@[expose, rust_fun "core::cmp::impls::{core::cmp::PartialEq<bool, bool>}::eq"]
def core.cmp.impls.PartialEqBool.eq (b0 b1 : Bool) : Result Bool := .ok (b0 = b1)

@[expose, reducible, rust_trait_impl "core::cmp::PartialEq<bool, bool>"]
def core.cmp.PartialEqBool : core.cmp.PartialEq Bool Bool := {
  eq := core.cmp.impls.PartialEqBool.eq
}

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialEq<&'a @A, &'b @B>}::eq"]
def core.cmp.impls.PartialEqShared.eq {A : Type _} {B : Type _} (PartialEqInst : core.cmp.PartialEq A B)
  (x : A) (y : B) : Result Bool :=
  PartialEqInst.eq x y

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialEq<&'a @A, &'b @B>}::ne"]
def core.cmp.impls.PartialEqShared.ne {A : Type _} {B : Type _} (PartialEqInst : core.cmp.PartialEq A B)
  (x : A) (y : B) : Result Bool :=
  PartialEqInst.ne x y

@[expose, reducible, rust_trait_impl "core::cmp::PartialEq<&'a @A, &'b @B>"]
def core.cmp.PartialEqShared {A : Type _} {B : Type _}
  (PartialEqInst : core.cmp.PartialEq A B) : core.cmp.PartialEq A B := {
  eq := core.cmp.impls.PartialEqShared.eq PartialEqInst
  ne := core.cmp.impls.PartialEqShared.ne PartialEqInst
}

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'a @A, &'b @B>}::partial_cmp"]
def core.cmp.impls.PartialOrdShared.partial_cmp {A : Type _} {B : Type _}
  (PartialOrdInst : core.cmp.PartialOrd A B) (x : A) (y : B) : Result (Option Ordering) :=
  PartialOrdInst.partial_cmp x y

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'a @A, &'b @B>}::lt"]
def core.cmp.impls.PartialOrdShared.lt {A : Type _} {B : Type _}
  (PartialOrdInst : core.cmp.PartialOrd A B) (x : A) (y : B) : Result Bool :=
  PartialOrdInst.lt x y

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'a @A, &'b @B>}::le"]
def core.cmp.impls.PartialOrdShared.le {A : Type _} {B : Type _}
  (PartialOrdInst : core.cmp.PartialOrd A B) (x : A) (y : B) : Result Bool :=
  PartialOrdInst.le x y

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'a @A, &'b @B>}::gt"]
def core.cmp.impls.PartialOrdShared.gt {A : Type _} {B : Type _}
  (PartialOrdInst : core.cmp.PartialOrd A B) (x : A) (y : B) : Result Bool :=
  PartialOrdInst.gt x y

@[expose, simp, rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'a @A, &'b @B>}::ge"]
def core.cmp.impls.PartialOrdShared.ge {A : Type _} {B : Type _}
  (PartialOrdInst : core.cmp.PartialOrd A B) (x : A) (y : B) : Result Bool :=
  PartialOrdInst.ge x y

@[expose, reducible, rust_trait_impl "core::cmp::PartialOrd<&'a @A, &'b @B>"]
def core.cmp.PartialOrdShared {A : Type _} {B : Type _}
  (PartialOrdInst : core.cmp.PartialOrd A B) : core.cmp.PartialOrd A B := {
  partialEqInst := core.cmp.PartialEqShared PartialOrdInst.partialEqInst
  partial_cmp := core.cmp.impls.PartialOrdShared.partial_cmp PartialOrdInst
  lt := core.cmp.impls.PartialOrdShared.lt PartialOrdInst
  le := core.cmp.impls.PartialOrdShared.le PartialOrdInst
  gt := core.cmp.impls.PartialOrdShared.gt PartialOrdInst
  ge := core.cmp.impls.PartialOrdShared.ge PartialOrdInst
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

end Aeneas.Std
