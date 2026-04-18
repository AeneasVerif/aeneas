-- Correctness proof for the docs-example test in `SliceConcat.lean`.

import SliceConcat
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace slice_concat

/-- `<[V]>::concat` flattens a slice of vectors into a single vector via
the `Concat<V, Vec<T>>` impl and the `Borrow<Vec<T>, [T]>` blanket. -/
theorem test_concat_correct :
    test_concat ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end slice_concat
