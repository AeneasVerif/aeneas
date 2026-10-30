module
public import Aeneas
public import ArrayIterMut.ArrayIterMut
public section

open Aeneas Aeneas.Std Result core.slice.iter

/-! Proofs for the `IntoIterator for &mut [T; N]` and `IterMut::next` examples. -/

namespace array_iter_mut

/-- `add_two` adds `2` to every element of the array (when this doesn't overflow): the
documentation example `[1, 2, 4]` becomes `[3, 4, 6]`. The loop is handled by the spec of
`for x in it { *x = g(*x) }` loops over `IterMut`, with `g = (· + 2)`. -/
theorem add_two_spec {N : Std.Usize} (x : Array Std.I32 N)
    (h : ∀ j < N.val, (x.val[j]!).val + 2 ≤ Std.I32.max) :
    add_two x ⦃ y => ∀ j < N.val, (y.val[j]!).val = (x.val[j]!).val + 2 ⦄ := by
  unfold add_two add_two_loop
  step
  step with core.slice.iter.IterMut.loop_updateBody.spec (fun e => e + 2#i32)
    (fun _ x (y : Std.I32) => y.val = x.val + 2) add_two_loop.body iter iter_post1
    by (intro j hj; have := h j (by simpa [Slice.length, iter_post] using hj)
        rw [iter_post]; step*)
  intro j hj
  have hn : iter.slice.length = N.val := by simp [Slice.length, iter_post]
  rw [iter_post2 back (by rw [back_post, hn]), back_post1 j (by rw [hn]; exact hj), iter_post]

end array_iter_mut
