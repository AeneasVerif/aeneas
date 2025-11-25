import Aeneas.Std.Core.Fmt

namespace Aeneas.Std

@[rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap"]
def core.result.Result.unwrap {T E : Type}
  (_ : core.fmt.Debug T) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

end Aeneas.Std
