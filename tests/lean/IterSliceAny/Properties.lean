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

end iter_slice_any
