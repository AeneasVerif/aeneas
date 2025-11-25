import Aeneas.Std.Core.Core

namespace Aeneas.Std

@[rust_type "core::fmt::Arguments"]
def core.fmt.Arguments : Type := Unit

@[rust_type "core::fmt::rt::Argument"]
def core.fmt.rt.Argument : Type := Unit

@[reducible, rust_type "core::fmt::Error"]
def core.fmt.Error := Unit

/- TODO: -/
@[rust_type "core::fmt::Formatter"]
axiom core.fmt.Formatter : Type

@[rust_trait "core::fmt::Debug"]
structure core.fmt.Debug (T : Type) where
  fmt : T → Formatter → Result (Formatter × Formatter → Formatter)

@[rust_trait "core::fmt::Display"]
structure core.fmt.Display (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_trait "core::fmt::LowerHex"]
structure core.fmt.LowerHex (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

end Aeneas.Std
