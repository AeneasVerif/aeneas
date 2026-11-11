module

public import Mathlib.Data.List.Nodup

/-!
# A list without duplicates is ordered by position

## Main statements

* `List.Nodup.pairwise_idxOf_lt`: in a list without duplicates, each element comes, by `idxOf`,
  before the elements after it.
-/

@[expose] public section

namespace List

variable {α : Type*} [BEq α] [LawfulBEq α] {l : List α}

theorem Nodup.pairwise_idxOf_lt (hnd : l.Nodup) :
    l.Pairwise (fun a b => l.idxOf a < l.idxOf b) := by
  rw [pairwise_iff_getElem]
  intro i j hi hj hij
  rwa [hnd.idxOf_getElem, hnd.idxOf_getElem]

end List
