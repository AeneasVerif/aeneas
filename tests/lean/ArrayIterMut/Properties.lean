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

/-- The update uses a captured value `k`: the generated body takes it as an extra argument. -/
theorem add_k_spec {N : Std.Usize} (x : Array Std.I32 N) (k : Std.I32)
    (h : ∀ j < N.val,
      Std.I32.min ≤ (x.val[j]!).val + k.val ∧ (x.val[j]!).val + k.val ≤ Std.I32.max) :
    add_k x k ⦃ y => ∀ j < N.val, (y.val[j]!).val = (x.val[j]!).val + k.val ⦄ := by
  unfold add_k add_k_loop
  step
  step with core.slice.iter.IterMut.loop_updateBody.spec (fun e => e + k)
    (fun _ x (y : Std.I32) => y.val = x.val + k.val) (add_k_loop.body k) iter iter_post1
    by (intro j hj; have := h j (by simpa [Slice.length, iter_post] using hj)
        rw [iter_post]; step*)
  intro j hj
  have hn : iter.slice.length = N.val := by simp [Slice.length, iter_post]
  rw [iter_post2 back (by rw [back_post, hn]), back_post1 j (by rw [hn]; exact hj), iter_post]

/-- A conditional write: the update is the `if`, which never fails. -/
theorem cap_spec {N : Std.Usize} (x : Array Std.I32 N) (m : Std.I32) :
    cap x m ⦃ y => ∀ j < N.val, y.val[j]! = if x.val[j]! > m then m else x.val[j]! ⦄ := by
  unfold cap cap_loop
  step
  step with core.slice.iter.IterMut.loop_updateBody.spec
    (fun e => if e > m then ok m else ok e) (fun _ x (y : Std.I32) => y = if x > m then m else x)
    (cap_loop.body m) iter iter_post1
    by (intro j hj; split <;> simp_all)
  intro j hj
  have hn : iter.slice.length = N.val := by simp [Slice.length, iter_post]
  rw [iter_post2 back (by rw [back_post, hn]), back_post1 j (by rw [hn]; exact hj), iter_post]

end array_iter_mut
