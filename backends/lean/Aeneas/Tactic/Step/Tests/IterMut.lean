module
import Aeneas.Std.SliceIter
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace iter_mut

/- `(&mut a).into_iter()` for an array `a`: the iterator ranges over the array, and the backward
function writes the iterator's slice back into the array. -/
example (a : Array U32 4#usize) :
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a
      ⦃ it back => it.slice.val = a.val ∧ (back it).val = a.val ⦄ := by
  step*
  simp_all

/- One step of an `IterMut` over a non-empty slice: the first element, and a back function which
writes it. -/
example (s : Slice U32) (h : 0 < s.length) :
    core.slice.iter.IteratorIterMut.next { slice := s }
      ⦃ o it back => o = some s.val[0] ∧ it.i = 1 ∧
        (back it (some 7#u32)).slice.val[0]! = 7#u32 ⦄ := by
  step*
  simp_all

end iter_mut
