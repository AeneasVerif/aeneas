import Aeneas.Std.Core.Core
import Aeneas.Std.Core.Result
import Aeneas.Std.Core.Ops

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
  fromInst.from_ x

@[reducible, rust_trait_impl "core::convert::Into<@Self, @T>"]
def core.convert.IntoFrom {T : Type} {U : Type} (fromInst : core.convert.From U T)
  : core.convert.Into T U := {
  into := core.convert.IntoFrom.into fromInst
}

@[simp, step_simps, rust_fun "core::convert::{core::convert::From<@T, @T>}::from" -canFail]
def core.convert.FromSame.from_ {T : Type} (x : T) : T := x

@[reducible, rust_trait_impl "core::convert::From<@Self, @Self>"]
def core.convert.FromSame (T : Type) : core.convert.From T T := {
  from_ := fun x => ok (core.convert.FromSame.from_ x)
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

/-! ### `Try<T, Result<Infallible, E>> for Result<T, E>`

The `?` operator on a `Result<T, E>` desugars to `Try::branch`, which returns
`ControlFlow<Residual, Output>`. For `Result<T, E>`, the residual type is
`Result<Infallible, E>` (it can only carry an error). This impl is defined
here (not in `Core/Result.lean`) because it references `Infallible`, which is
declared in this file — see the note at the end of `Core/Result.lean`.
-/

/-- `Try<Result<Infallible, E>>::branch` for `Result<T, E>`.

- Docs: https://doc.rust-lang.org/std/ops/trait.Try.html#tymethod.branch
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs
-/
@[rust_fun
  "core::result::{core::ops::try_trait::Try<core::result::Result<@T, @E>, @T, core::result::Result<core::convert::Infallible, @E>>}::branch"]
def core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch
    {T E : Type} (self : core.result.Result T E) :
    Aeneas.Std.Result (core.ops.control_flow.ControlFlow
      (core.result.Result core.convert.Infallible E) T) :=
  match self with
  | .Ok v => .ok (.Continue v)
  | .Err e => .ok (.Break (.Err e))

/-- `Try::from_output` for `Result<T, E>`: wraps the output in `Ok`. -/
def core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.from_output
    {T E : Type} (output : T) :
    Aeneas.Std.Result (core.result.Result T E) :=
  .ok (.Ok output)

/-- `FromResidual` for `Result<T, F>` given residual `Result<Infallible, E>`
via a `From<E> -> F` conversion. Rust impl:
```text
impl<T, E, F: From<E>> FromResidual<Result<Infallible, E>> for Result<T, F>
```
-/
@[rust_fun
  "core::result::{core::ops::try_trait::FromResidual<core::result::Result<@T, @F>, core::result::Result<core::convert::Infallible, @E>>}::from_residual"]
def core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
    (T : Type) {E F : Type}
    (convertFromInst : core.convert.From F E)
    (residual : core.result.Result core.convert.Infallible E) :
    Aeneas.Std.Result (core.result.Result T F) :=
  match residual with
  | .Err e => do
    let f ← convertFromInst.from_ e
    .ok (.Err f)
  -- Unreachable: `Infallible` has no inhabitants.
  | .Ok v => nomatch v

@[reducible, rust_trait_impl
  "core::ops::try_trait::FromResidual<core::result::Result<@T, @F>, core::result::Result<core::convert::Infallible, @E>>"]
def core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE
    (T : Type) {E F : Type} (convertFromInst : core.convert.From F E) :
    core.ops.try_trait.FromResidual
      (core.result.Result T F)
      (core.result.Result core.convert.Infallible E) := {
  from_residual :=
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T
      convertFromInst
}

@[reducible, rust_trait_impl
  "core::ops::try_trait::Try<core::result::Result<@T, @E>, @T, core::result::Result<core::convert::Infallible, @E>>"]
def core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE
    (T E : Type) :
    core.ops.try_trait.Try
      (core.result.Result T E) T
      (core.result.Result core.convert.Infallible E) := {
  FromResidualInst :=
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE T
      (core.convert.FromSame E)
  from_output :=
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.from_output
  branch :=
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch
}

end Aeneas.Std
