import Aeneas.Std.Core.Core
import Aeneas.Std.Core.Result

namespace Aeneas.Std

@[reducible, rust_type "core::fmt::Error"]
def core.fmt.Error := Unit

/- TODO: -/
@[rust_type "core::fmt::Formatter"]
axiom core.fmt.Formatter : Type

@[rust_trait "core::fmt::Debug"]
structure core.fmt.Debug (T : Type) where
  fmt : T → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

-- TODO: move?
@[rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap"]
def core.result.Result.unwrap {T E : Type}
  (_ : core.fmt.Debug T) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

@[rust_type "core::fmt::Arguments"]
def core.fmt.Arguments : Type := Unit

@[rust_type "core::fmt::rt::Argument"]
def core.fmt.rt.Argument : Type := Unit

@[rust_trait "core::fmt::Display"]
structure core.fmt.Display (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_trait "core::fmt::LowerHex"]
structure core.fmt.LowerHex (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"]
def core.fmt.Formatter.write_str (fmt : core.fmt.Formatter) (_ : Str) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"]
def core.fmt.Formatter.write_fmt
  (fmt : core.fmt.Formatter) (_ : core.fmt.Arguments) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: we should update something in the formatter, once we have a model for it
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"]
def core.fmt.DebugShared.fmt {T : Type} (DebugInst : core.fmt.Debug T) (x : T)
  (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  DebugInst.fmt x fmt

@[rust_fun "core::fmt::{core::fmt::Debug<bool>}::fmt"]
def core.fmt.DebugBool.fmt (_ : Bool) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::{core::fmt::Debug<()>}::fmt"]
def core.fmt.DebugUnit.fmt (_ : Unit) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

end Aeneas.Std
