module
public import Aeneas
public import IterSliceAny
public section

open Aeneas Aeneas.Std Result

namespace iter_slice_any

/-- A translated client of `slice::Iter::any`. -/
theorem any_reports_nonzero_spec :
    any_reports_nonzero ⦃ b => b = true ⦄ := by
  unfold any_reports_nonzero
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ i, s_post, i_post ⟩ ← core.slice.Slice.iter.spec
  let* ⟨ b, _, b_post, _, _ ⟩ ←
    core.slice.iter.IteratorSliceIter.any.spec (p := fun x => x != 0#u8)
  case hf =>
    intro x _
    simp [any_reports_nonzero.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut]
  simp_all [Array.to_slice, Array.make_val]

/-- `any` returns false on an empty translated slice. -/
theorem any_on_empty_slice_spec :
    any_on_empty_slice ⦃ _ => True ⦄ := by
  unfold any_on_empty_slice
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ iter, s_post, iter_post ⟩ ← core.slice.Slice.iter.spec
  let* ⟨ b, _, b_post, _, _ ⟩ ←
    core.slice.iter.IteratorSliceIter.any.spec (p := fun _ => true)
  case hf =>
    intro x _
    simp [any_on_empty_slice.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut]
  step*
  case h =>
    simp_all [Array.to_slice]

/-- After a match, `any` leaves the following element for `next`. -/
theorem any_stops_after_match_spec :
    any_stops_after_match ⦃ _ => True ⦄ := by
  unfold any_stops_after_match
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ iter, s_post, iter_post ⟩ ← core.slice.Slice.iter.spec
  let* ⟨ b, iter1, b_post, _, rest_post ⟩ ←
    core.slice.iter.IteratorSliceIter.any.spec (p := fun x => x != 0#u8)
  case hf =>
    intro x _
    simp [any_stops_after_match.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut]
  simp_all [Array.to_slice, Array.make_val]
  have hi : iter1.i = 2 := by
    have h := congrArg List.length rest_post
    simp at h
    omega
  unfold core.slice.iter.IteratorSliceIter.next
  step*
  all_goals simp_all [core.option.Option.unwrap, massert, WP.spec_ok]

/-- When no element matches, `any` leaves the translated iterator exhausted. -/
theorem any_exhausts_without_match_spec :
    any_exhausts_without_match ⦃ _ => True ⦄ := by
  unfold any_exhausts_without_match
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ iter, s_post, iter_post ⟩ ← core.slice.Slice.iter.spec
  let* ⟨ b, iter1, b_post, _, rest_post ⟩ ←
    core.slice.iter.IteratorSliceIter.any.spec (p := fun x => x != 0#u8)
  case hf =>
    intro x _
    simp [any_exhausts_without_match.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut]
  simp_all [Array.to_slice, Array.repeat_val]
  have hdone : ¬ iter1.i < 2 := by omega
  unfold core.slice.iter.IteratorSliceIter.next
  simp_all
  simp [show ¬ iter1.i ≤ 1 by omega, massert, WP.spec_ok]

/-- The owned predicate state advances until the second call, leaving the final element. -/
theorem any_threads_owned_predicate_state_spec :
    any_threads_owned_predicate_state ⦃ _ => True ⦄ := by
  unfold any_threads_owned_predicate_state
  simp [lift, Array.to_slice, Array.make_val, core.slice.Slice.iter,
    core.slice.iter.IteratorSliceIter.any, core.slice.iter.IteratorSliceIter.any.loop,
    any_threads_owned_predicate_state.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut,
    core.slice.iter.IteratorSliceIter.next, core.option.Option.unwrap, massert]
  step*
  have hx : x = 1#u8 := by scalar_tac
  subst x
  simp
  step*
  have hx : x = 2#u8 := by scalar_tac
  subst x
  step*
  simp
  have hval : (Array.to_slice (Array.make 3#usize [10#u8, 20#u8, 30#u8]))[2] = 30#u8 := by
    rfl
  change (if (Array.to_slice (Array.make 3#usize [10#u8, 20#u8, 30#u8]))[2] = 30#u8
    then ok () else fail Error.assertionFailure) ⦃ _ => True ⦄
  simp [hval, WP.spec_ok]

end iter_slice_any
