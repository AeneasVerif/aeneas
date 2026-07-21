module
public import Aeneas.Std.Slice
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.String
public section

namespace Aeneas.Std

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_fields_finish"]
def core.fmt.Formatter.debug_struct_fields_finish :
  core.fmt.Formatter → Str → Slice Str →
    Slice (Dyn (fun _dyn => core.fmt.Debug _dyn)) →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model
  fun fmt _ _ _ =>
  .ok (.Ok (), fmt)

end Aeneas.Std
