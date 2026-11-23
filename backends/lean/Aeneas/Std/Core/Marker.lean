module
public import Aeneas.Std.Core.Core
public section

namespace Aeneas.Std

@[rust_trait "core::marker::StructuralPartialEq"]
structure core.marker.StructuralPartialEq (Self : Type _) where
deriving Lean.Order.CCPO

@[rust_trait "core::marker::Freeze"]
structure core.marker.Freeze (Self : Type _) where
deriving Lean.Order.CCPO

end Aeneas.Std
