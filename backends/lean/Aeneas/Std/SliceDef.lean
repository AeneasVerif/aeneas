module
public import Aeneas.Std.Scalar.Core
public section

namespace Aeneas.Std

def Slice (α : Type u) := { l : List α // l.length ≤ Usize.max }

end Aeneas.Std
