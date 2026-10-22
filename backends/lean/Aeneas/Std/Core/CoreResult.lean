module
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Core.Result
public meta import Aeneas.Tactic.Step.Init

public section

namespace Aeneas.Std

open Result

/-- Pure model of `Result::map_err`: leaves `Ok` untouched and maps the payload
    of `Err` through `fnOnce`. -/
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F)
  (x : core.result.Result T E) (f : O) :
  Std.Result (core.result.Result T F) :=
  match x with
  | .Ok value => ok (.Ok value)
  | .Err error => do
      let mapped ← fnOnce.call_once f error
      ok (.Err mapped)

@[simp]
theorem core.result.Result.map_err_ok
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F) (value : T) (f : O) :
  core.result.Result.map_err fnOnce (.Ok value) f =
    ok (core.result.Result.Ok value : core.result.Result T F) := rfl

@[simp]
theorem core.result.Result.map_err_err
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F) (error : E) (f : O) :
  core.result.Result.map_err fnOnce
      (core.result.Result.Err error : core.result.Result T E) f = (do
    let mapped ← fnOnce.call_once f error
    ok (core.result.Result.Err mapped : core.result.Result T F)) := rfl

/-- Pure model of `Result::unwrap_or`: the payload of `Ok`, or `default` on
    `Err`. -/
@[expose, step_pure_def, rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap_or" -canFail]
def core.result.Result.unwrap_or {T E : Type _} (x : core.result.Result T E) (default : T) : T :=
  match x with
  | .Ok value => value
  | .Err _ => default

@[simp]
theorem core.result.Result.unwrap_or_ok {T E : Type _} (value default : T) :
  core.result.Result.unwrap_or (.Ok value : core.result.Result T E) default = value := rfl

@[simp]
theorem core.result.Result.unwrap_or_err {T E : Type _} (error : E) (default : T) :
  core.result.Result.unwrap_or (.Err error : core.result.Result T E) default = default := rfl

end Aeneas.Std
