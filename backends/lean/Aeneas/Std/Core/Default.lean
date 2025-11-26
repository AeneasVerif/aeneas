import Aeneas.Std.Primitives

namespace Aeneas.Std

@[rust_trait "core::default::Default"]
structure core.default.Default (Self : Type) where
  default : Result Self

@[rust_fun "core::default::{core::default::Default<bool>}::default"]
def core.default.DefaultBool.default : Result Bool := .ok false

end Aeneas.Std
