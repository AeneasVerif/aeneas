import Aeneas.Std.Core.Core
import Aeneas.Std.Core.Result
import Aeneas.Std.Core.Ops
import Aeneas.Tactic.Step.Init

namespace Aeneas.Std

open Result

@[rust_type "core::convert::Infallible"]
inductive core.convert.Infallible where

@[rust_trait "core::convert::Into"]
structure core.convert.Into (Self : Type) (T : Type) where
  into : Self → Result T

@[reducible, simp, step_simps, rust_fun "core::convert::{core::convert::Into<@T, @U>}::into"]
def core.convert.IntoFrom.into {T : Type} {U : Type}
  (fromInst : core.convert.From U T) (x : T) : Result U :=
  fromInst.from x

@[reducible, rust_trait_impl "core::convert::Into<@Self, @T>"]
def core.convert.IntoFrom {T : Type} {U : Type} (fromInst : core.convert.From U T)
  : core.convert.Into T U := {
  into := core.convert.IntoFrom.into fromInst
}

@[rust_trait "core::convert::AsRef"]
structure core.convert.AsRef (Self : Type) (T : Type) where
  as_ref : Self → Result T

@[simp, step_simps, rust_fun "core::convert::{core::convert::From<@T, @T>}::from" -canFail]
def core.convert.FromSame.from {T : Type} (x : T) : T := x

@[reducible, rust_trait_impl "core::convert::From<@Self, @Self>"]
def core.convert.FromSame (T : Type) : core.convert.From T T := {
  «from» := fun x => ok (core.convert.FromSame.from x)
}

@[rust_trait "core::convert::TryFrom"]
structure core.convert.TryFrom (Self T Error : Type) where
  try_from : T → Result (core.result.Result Self Error)

@[rust_fun "core::convert::{core::convert::TryInto<@T, @U, @Error>}::try_into"]
def core.convert.TryInto.Blanket.try_into
  {T : Type} {U : Type} {Error : Type} (TryFromInst : core.convert.TryFrom U T Error) (x : T) :
  Result (core.result.Result U Error) :=
  TryFromInst.try_from x

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

@[reducible, rust_trait_impl "core::convert::TryInto<@T, @U, @E>"]
def core.convert.TryInto.Blanket {T U E : Type}
  (TryFromInst : core.convert.TryFrom U T E) :
  core.convert.TryInto T U E := {
  try_into := core.convert.TryInto.Blanket.try_into TryFromInst
}

@[rust_trait "core::convert::AsMut"]
structure core.convert.AsMut (Self : Type) (T : Type) where
  as_mut : Self → Result (T × (T → Self))

@[reducible, rust_trait_impl "core::convert::AsMut<Box<@T>, @T>"]
def core.convert.AsMutBox (T : Type) : core.convert.AsMut T T := {
  as_mut := fun x => ok (alloc.boxed.AsMutBox.as_mut x)
}

/-- `Result::is_ok`: `true` on `Ok`, `false` on `Err`. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_ok"]
def core.result.Result.is_ok {T E : Type} :
    core.result.Result T E → Std.Result Bool
  | .Ok _ => .ok true
  | .Err _ => .ok false

def core.result.Result.ok? {T E : Type} (r : core.result.Result T E) : Bool :=
  match r with
  | .Ok _ => true
  | .Err _ => false

@[simp, grind =, agrind =]
theorem core.result.Result.ok?_Ok {T E : Type} (x : T) :
  (core.result.Result.Ok x : core.result.Result T E).ok? = true := by grind [ok?]

@[simp, grind =, agrind =]
theorem core.result.Result.ok?_Err {T E : Type} (e : E) :
  (core.result.Result.Err e : core.result.Result T E).ok? = false := by grind [ok?]

/-- `Result::branch` (`Try`): `Ok v ⇒ Continue v`, `Err e ⇒ Break (Err e)`. -/
@[rust_fun
  "core::result::{core::ops::try_trait::Try<core::result::Result<@T, @E>>}::branch"]
def core.result.Result.Insts.CoreOpsTry.branch
  {T E : Type} :
  core.result.Result T E →
    Std.Result (core.ops.control_flow.ControlFlow
      (core.result.Result core.convert.Infallible E) T)
  | .Ok v => .ok (.Continue v)
  | .Err e => .ok (.Break (.Err e))

/-- `Result::from_residual` (`FromResidual`): converts an `Err`-residual,
    applying the `From` instance to the error. -/
@[rust_fun
  "core::result::{core::ops::try_trait::FromResidual<core::result::Result<@T, @F>, core::result::Result<core::convert::Infallible, @E>>}::from_residual"]
def core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  (T : Type) {E F : Type} (convertFromInst : core.convert.From F E)
  (r : core.result.Result core.convert.Infallible E) : Std.Result (core.result.Result T F) :=
  match r with
  | .Ok x => x.casesOn
  | .Err e => do
      let v ← convertFromInst.from e
      .ok (.Err v)

/-- Step spec for `Result::is_ok`: returns `true` iff the input is `Ok`. -/
@[step]
theorem core.result.Result.is_ok.step_spec {T E : Type}
    (r : core.result.Result T E) :
    core.result.Result.is_ok r
    ⦃ (b : Bool) => b = r.ok? ⦄ := by
  match r with
  | .Ok v => grind [is_ok]
  | .Err e => grind [is_ok]

/-- Step spec for `Result::branch` on an `Ok`: yields `Continue v`. -/
theorem core.result.Result.Insts.CoreOpsTry.branch_Ok.spec
    {T E : Type} (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch (T := T) (E := E) (.Ok v)
    ⦃ (cf : core.ops.control_flow.ControlFlow
              (core.result.Result core.convert.Infallible E) T) =>
        cf = .Continue v ⦄ := by
  exact (WP.spec_ok _).mpr rfl

/-- Step spec for `Result::branch` on an `Err`: yields `Break (Err e)`. -/
theorem core.result.Result.Insts.CoreOpsTry.branch_Err.spec
    {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry.branch (T := T) (E := E) (.Err e)
    ⦃ (cf : core.ops.control_flow.ControlFlow
              (core.result.Result core.convert.Infallible E) T) =>
        cf = .Break (.Err e) ⦄ := by
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem core.result.Result.Insts.CoreOpsTry.branch.step_spec
    {T E : Type} (r : core.result.Result T E) :
    core.result.Result.Insts.CoreOpsTry.branch r
    ⦃ (cf : core.ops.control_flow.ControlFlow
              (core.result.Result core.convert.Infallible E) T) =>
        match r with
        | .Ok v => cf = .Continue v
        | .Err e => cf = .Break (.Err e) ⦄ := by
  match h: r with
  | .Ok v => simp [CoreOpsTry.branch]
  | .Err e => simp [CoreOpsTry.branch]

/-- Step spec for `Result::from_residual` on an `Err`: applies the `From`
    conversion to the error.

    Note that as `core.convert.Infallible` is an empty type the `.Ok` case is not possible.
-/
@[step]
theorem
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual_Err.spec
    (T : Type) {E F : Type} (convertFromInst : core.convert.From F E)
    (e : E) (v : F) (hfrom : convertFromInst.from e = .ok v) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      T convertFromInst (.Err e)
    ⦃ (out : core.result.Result T F) => out = .Err v ⦄ := by
  simp [from_residual, hfrom]

@[step]
theorem
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual.spec
    (T : Type) {E F : Type} (convertFromInst : core.convert.From F E)
    (r : Result convert.Infallible E) (hfrom : ∀ e, r = .Err e → ∃ v, convertFromInst.from e = .ok v) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      T convertFromInst r
    ⦃ (out : core.result.Result T F) => ∃ e v, r = .Err e ∧ convertFromInst.from e = .ok v ∧ out = .Err v ⦄ := by
  match h: r with
  | .Ok x => cases x
  | .Err e =>
    simp at hfrom
    obtain ⟨ v, hfrom ⟩ := hfrom
    simp [from_residual, hfrom]

end Aeneas.Std
