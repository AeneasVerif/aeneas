/- `alloc::string` -/
module
public import Lean
public meta import Aeneas.Extract.Extract
public import Aeneas.Std.Primitives
public section

attribute [rust_type "alloc::string::String" (body := .opaque)] String
