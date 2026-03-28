import Aeneas.Std.Core.Core
import Aeneas.Std.String

namespace Aeneas.Std

/-- Returns the contained `some` value. The message is ignored: on `none`, this
    fails with `Error.panic`, which is the same behavior as `unwrap`. -/
@[rust_fun "core::option::{core::option::Option<@T>}::expect"]
def core.option.Option.expect {T : Type} (x : Option T) (_msg: Str) : Result T :=
  Result.ofOption x Error.panic

theorem core.option.Option.expect.spec {T : Type} (x : Option T) (msg: Str) (h : x.isSome) :
  expect x msg ⦃ v => x = some v ⦄ := by
  simp only [expect, Result.ofOption]; grind

end Aeneas.Std
