module
import Aeneas.Std.SliceIter
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace iter_mut

/- `(&mut a).into_iter()` for an array `a`: the iterator ranges over the array, and the backward
function writes the iterator's slice back into the array. -/
example (a : Array U32 4#usize) :
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a
      ⦃ it back => it.slice.val = a.val ∧ (back it) = a ⦄ := by
  step*
  refine ⟨it_post, Aeneas.Std.Array.ext _ _ ?_⟩
  rw [it_post2 it (by simp [it_post]), it_post]

end iter_mut
