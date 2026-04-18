-- Correctness proofs for docs-example tests in `VecMethods.lean`.
--
-- Structural proofs: simp to expose the vec constructor, then `step*`
-- discharges `push_spec` side conditions; trailing `simp_all` + `rfl`
-- finishes the residual `len / as_slice` equalities.

import VecMethods

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow Error

namespace vec_methods

/-- `Vec::new().is_empty()` yields `true`. -/
theorem test_vec_is_empty_new_correct :
    test_vec_is_empty_new ⦃ _ => True ⦄ := by
  simp [test_vec_is_empty_new, make_empty, alloc.vec.Vec.new,
    alloc.vec.Vec.is_empty]

/-- After `push`, `is_empty` yields `false`. -/
theorem test_vec_is_empty_after_push_correct :
    test_vec_is_empty_after_push ⦃ _ => True ⦄ := by
  simp [test_vec_is_empty_after_push, make_empty, alloc.vec.Vec.new]
  step*

/-- `Vec::clear` makes the vector empty. -/
theorem test_vec_clear_correct :
    test_vec_clear ⦃ _ => True ⦄ := by
  simp [test_vec_clear, alloc.vec.Vec.with_capacity]
  step*
  simp_all [alloc.vec.Vec.clear, alloc.vec.Vec.is_empty]

/-- `Vec::truncate(n)` shortens the vector to `n` elements when `n < len`. -/
theorem test_vec_truncate_shortens_correct :
    test_vec_truncate_shortens ⦃ _ => True ⦄ := by
  simp [test_vec_truncate_shortens, alloc.vec.Vec.with_capacity]
  step* <;> first
    | scalar_tac
    | (simp_all [alloc.vec.Vec.truncate, alloc.vec.Vec.len]; rfl)

/-- `Vec::truncate(n)` is a no-op when `n >= len`. -/
theorem test_vec_truncate_noop_if_longer_correct :
    test_vec_truncate_noop_if_longer ⦃ _ => True ⦄ := by
  simp [test_vec_truncate_noop_if_longer, alloc.vec.Vec.with_capacity]
  step* <;> first
    | scalar_tac
    | (simp_all [alloc.vec.Vec.truncate, alloc.vec.Vec.len]; rfl)

/-- `Vec::as_slice` returns a slice with the same contents. -/
theorem test_vec_as_slice_correct :
    test_vec_as_slice ⦃ _ => True ⦄ := by
  simp [test_vec_as_slice, alloc.vec.Vec.with_capacity]
  step* <;> first
    | scalar_tac
    | (simp_all [alloc.vec.Vec.as_slice, Slice.len]; rfl)

/-- `Vec::remove(i)` pulls out element `i` and shifts the rest. -/
theorem test_vec_remove_middle_correct :
    test_vec_remove_middle ⦃ _ => True ⦄ := by
  simp [test_vec_remove_middle, alloc.vec.Vec.with_capacity]
  step* <;> first
    | scalar_tac
    | (simp_all [alloc.vec.Vec.remove]; step*)

/-- `Vec::append(&mut other)` moves all elements from `other` into `self`. -/
theorem test_vec_append_correct :
    test_vec_append ⦃ _ => True ⦄ := by
  simp [test_vec_append, alloc.vec.Vec.with_capacity]
  step* <;> first
    | scalar_tac
    | (simp_all [alloc.vec.Vec.append]
       split
       · step*
       · scalar_tac)

/-- `Vec::split_off(i)` returns a new vec with elements `[i..]`, leaving
`[0..i)` in `self`. -/
theorem test_vec_split_off_correct :
    test_vec_split_off ⦃ _ => True ⦄ := by
  simp [test_vec_split_off, alloc.vec.Vec.with_capacity]
  step* <;> first
    | scalar_tac
    | (simp_all [alloc.vec.Vec.split_off]; step*)

/-- `Vec::default()` returns an empty vector. -/
theorem test_vec_default_correct :
    test_vec_default ⦃ _ => True ⦄ := by
  simp [test_vec_default, alloc.vec.Vec.Insts.CoreDefaultDefault.default,
    alloc.vec.Vec.is_empty]

end vec_methods
