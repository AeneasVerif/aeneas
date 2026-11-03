module

public import Aeneas

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_matrix_view

/- Extracted from `raw_matrix_view::Matrix`. Alignment is carried by its
   explicit representation descriptor, not by this functional type. -/
@[reducible]
def Matrix := Array (Array U32 16#usize) 2#usize

end raw_matrix_view
