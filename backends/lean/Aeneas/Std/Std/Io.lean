module
public import Aeneas.Std.Core.Fmt
public section

namespace Aeneas.Std

@[rust_fun "std::io::stdio::_print"]
def std.io.stdio._print (_ : core.fmt.Arguments) : Result Unit := .ok ()

end Aeneas.Std
