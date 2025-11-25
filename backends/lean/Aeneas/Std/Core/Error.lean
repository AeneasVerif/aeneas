import Aeneas.Std.Core.Fmt

namespace Aeneas.Std

@[rust_trait "core::error::Error" (parentClauses := ["fmtDebugInst", "fmtDisplayInst"])]
structure core.error.Error (Self : Type) where
  fmtDebugInst : core.fmt.Debug Self
  fmtDisplayInst : core.fmt.Display Self

end Aeneas.Std
