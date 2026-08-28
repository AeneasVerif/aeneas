import Aeneas.Std.Core.Ops
import Aeneas.Std.Core.Result

namespace Aeneas.Std

open Result

/-- Pure model of `Result::map_err`: leaves `Ok` untouched and maps the payload
    of `Err` through `fnOnce`. The mapping call itself lives in the `Result`
    monad, so `map_err` can fail whenever `fnOnce` does. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
  {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F)
  (x : core.result.Result T E) (f : O) :
  Std.Result (core.result.Result T F) :=
  match x with
  | .Ok value => ok (.Ok value)
  | .Err error => do
      let mapped ← fnOnce.call_once f error
      ok (.Err mapped)

/-! The two equations below expose the model to `simp` before `step` processes
    the surrounding control flow. -/

@[simp]
theorem core.result.Result.map_err_ok
  {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F) (value : T) (f : O) :
  core.result.Result.map_err fnOnce (.Ok value) f =
    ok (core.result.Result.Ok value : core.result.Result T F) := rfl

@[simp]
theorem core.result.Result.map_err_err
  {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F) (error : E) (f : O) :
  core.result.Result.map_err fnOnce
      (core.result.Result.Err error : core.result.Result T E) f = (do
    let mapped ← fnOnce.call_once f error
    ok (core.result.Result.Err mapped : core.result.Result T F)) := rfl

end Aeneas.Std
