module

public import Aeneas

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_scale

/- Emitted functional type; the private padding and alignment live in rowRepr. -/
@[reducible]
def Row13 := Array U32 16#usize

end raw_scale
