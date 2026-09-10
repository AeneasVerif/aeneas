/- Arrays -/
module
public import Aeneas.Std.Array.Array
public import Aeneas.Std.Core.Fmt
public section

namespace Aeneas.Std

open Result

@[simp, rust_fun "core::array::{core::fmt::Debug<[@T; @N]>}::fmt"]
def core.array.DebugArray.fmt
  {T : Type} {N : Usize} (_ : core.fmt.Debug T) (_ : Array T N) (fmt : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: this model is simplistic
  ok (.Ok (), fmt)

@[reducible, rust_trait_impl "core::fmt::Debug<[@T; @N]>"]
def Array.Insts.CoreFmtDebug {T : Type} (N : Std.Usize)
  (fmtDebugInst : core.fmt.Debug T) : core.fmt.Debug (Array T N) := {
  fmt := core.array.DebugArray.fmt fmtDebugInst
}

end Aeneas.Std
