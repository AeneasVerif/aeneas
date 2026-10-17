/- `core::char` -/
module
public import Aeneas.Std.Core.Core
public section

namespace Aeneas.Std

/-- Whether the character is in the ASCII range (its code point is below `0x80`). -/
@[expose, step_pure_def, rust_fun "core::char::methods::{char}::is_ascii" -canFail]
def core.char.methods.Char.is_ascii (c : Char) : Bool := c.val < 0x80

end Aeneas.Std
