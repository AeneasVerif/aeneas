import Aeneas.Std.Core.Core
import Aeneas.Std.Core.Result
import Aeneas.Std.String

namespace Aeneas.Std

open Result

/-- Returns the contained `some` value. The message is ignored: on `none`, this
    fails with `Error.panic`, which is the same behavior as `unwrap`. -/
@[rust_fun "core::option::{core::option::Option<@T>}::expect"]
def core.option.Option.expect {T : Type} (x : Option T) (_msg: Str) : Result T :=
  Result.ofOption x Error.panic

attribute [agrind =] Option.isSome_none Option.isSome_some

theorem core.option.Option.expect.spec {T : Type} (x : Option T) (msg: Str) (h : x.isSome) :
  expect x msg ⦃ v => x = some v ⦄ := by
  simp only [expect, Result.ofOption]; grind

/-- Pure model of `Option::ok_or`: transforms `Option T` into
    `core.result.Result T E`, using `e` as the error on `none`. -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} (x : Option T) (e : E) :
  Result (core.result.Result T E) :=
  match x with
  | some value => ok (.Ok value)
  | none => ok (.Err e)

@[simp]
theorem core.option.Option.ok_or_some {T E : Type} (value : T) (error : E) :
  core.option.Option.ok_or (some value) error = ok (.Ok value) := rfl

@[simp]
theorem core.option.Option.ok_or_none {T E : Type} (error : E) :
  core.option.Option.ok_or (none : Option T) error = ok (.Err error) := rfl

end Aeneas.Std
