-- Spec proof for the auto-generated `test_enumerate_docs_example` in
-- `Enumerate.lean`. Written in Aeneas WP style: the postcondition
-- `⦃ _ => True ⦄` asserts that the function returns `.ok _` (any failure
-- branch makes `spec _ (_ => True) = False`).
--
-- This complements the `#assert` line in the auto-generated file by
-- producing an explicit, kernel-checked proof term that downstream code
-- can cite.

import Enumerate

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace enumerate

/-- The Rust docs example for `Iterator::enumerate`, translated through
Aeneas, succeeds: enumerating `['a', 'b', 'c']` yields
`(0, 'a'), (1, 'b'), (2, 'c')` followed by `none`.

See: <https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.enumerate>
-/
theorem test_enumerate_docs_example_correct :
    test_enumerate_docs_example ⦃ _ => True ⦄ := by
  unfold test_enumerate_docs_example
  step*
  -- 1st .next(): inner iter at i=0 yields some 'a'; count 0 → 1
  step with core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
      (item := 'a')
      (innerIter := ({ slice := s, i := 1 } : core.slice.iter.Iter Char))
      as ⟨ out1, hOpt1, hIter1, hCount1 ⟩
  case hInner =>
    show core.slice.iter.IteratorSliceIter.next iter.iter = _
    unfold core.slice.iter.IteratorSliceIter.next
    simp [iter_post1, i_post1, i_post2, s_post, Array.to_slice, Array.make]
  rw [hOpt1]
  simp [iter_post2]
  -- 2nd .next(): inner iter at i=1 yields some 'b'; count 1 → 2
  step with core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
      (item := 'b')
      (innerIter := ({ slice := s, i := 2 } : core.slice.iter.Iter Char))
      as ⟨ out2, hOpt2, hIter2, hCount2 ⟩
  case hInner =>
    show core.slice.iter.IteratorSliceIter.next out1.2.iter = _
    unfold core.slice.iter.IteratorSliceIter.next
    simp [hIter1, s_post, Array.to_slice, Array.make]
  rw [hOpt2]
  have : out1.2.count = 1#usize := by scalar_tac
  simp [this]
  -- 3rd .next(): inner iter at i=2 yields some 'c'; count 2 → 3
  step with core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
      (item := 'c')
      (innerIter := ({ slice := s, i := 3 } : core.slice.iter.Iter Char))
      as ⟨ out3, hOpt3, hIter3, hCount3 ⟩
  case hInner =>
    show core.slice.iter.IteratorSliceIter.next out2.2.iter = _
    unfold core.slice.iter.IteratorSliceIter.next
    simp [hIter2, s_post, Array.to_slice, Array.make]
  rw [hOpt3]
  have : out2.2.count = 2#usize := by scalar_tac
  simp [this]
  -- 4th .next(): inner iter at i=3 ≥ len, yields none
  step with core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
      (innerIter := ({ slice := s, i := 3 } : core.slice.iter.Iter Char))
      as ⟨ out4, hOpt4, hIter4, hCount4 ⟩
  case hInner =>
    show core.slice.iter.IteratorSliceIter.next out3.2.iter = _
    unfold core.slice.iter.IteratorSliceIter.next
    simp [hIter3, s_post, Array.to_slice, Array.make]
  rw [hOpt4]
  simp

end enumerate
