import Aeneas.Std.Core.Core
import Aeneas.Std.Core.Result

namespace Aeneas.Std

open Result

@[rust_type "core::convert::Infallible"]
inductive core.convert.Infallible where

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

@[rust_trait "core::convert::TryFrom"]
structure core.convert.TryFrom (Self T Error : Type) where
  try_from : T → Result (core.result.Result Self Error)

@[rust_fun "core::convert::{core::convert::TryInto<@T, @U, @Clause0_Error>}::try_into"]
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

@[rust_trait "core::convert::AsMut"]
structure core.convert.AsMut (Self : Type) (T : Type) where
  as_mut : Self → Result (T × (T → Self))

@[reducible, rust_trait_impl "core::convert::AsMut<Box<@T>, @T>"]
def core.convert.AsMutBox (T : Type) : core.convert.AsMut T T := {
  as_mut := fun x => ok (alloc.boxed.AsMutBox.as_mut x)
}

end Aeneas.Std
