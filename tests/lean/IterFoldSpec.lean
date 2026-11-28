import IterFold
import IterRfold

open Aeneas Aeneas.Std Result

namespace IterFoldSpec

theorem fold_slice_last : iter_fold.fold_slice_last ⦃ r => r = () ⦄ := by
  have hcall : ∀ acc x : Std.U32,
      iter_fold.fold_slice_last.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U32U32.call_mut
        () (acc, x) ⦃ r => r = (x, ()) ⦄ := by
    intro acc x
    simp [iter_fold.fold_slice_last.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U32U32.call_mut,
      WP.spec_ok]
  unfold iter_fold.fold_slice_last
  simp only [step_simps]
  let* ⟨s, s_post⟩ ← Array.to_slice.step_spec
  subst s
  simp [core.slice.Slice.iter]
  let* ⟨value, hvalue⟩ ← core.slice.iter.IteratorSliceIter.fold.spec
    iter_fold.fold_slice_last.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U32U32
    (fun _ x => x)
    ⟨(Array.make 3#usize [1#u32, 2#u32, 3#u32]).to_slice, 0⟩ 0#u32 () hcall
  simp [Array.to_slice, Array.make, hvalue, massert, WP.spec_ok]

theorem rfold_slice_last : iter_rfold.rfold_slice_last ⦃ r => r = () ⦄ := by
  have hcall : ∀ acc x : Std.U32,
      iter_rfold.rfold_slice_last.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U32U32.call_mut
        () (acc, x) ⦃ r => r = (x, ()) ⦄ := by
    intro acc x
    simp [iter_rfold.rfold_slice_last.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U32U32.call_mut,
      WP.spec_ok]
  unfold iter_rfold.rfold_slice_last
  simp only [step_simps]
  let* ⟨s, s_post⟩ ← Array.to_slice.step_spec
  subst s
  simp [core.slice.Slice.iter]
  let* ⟨value, hvalue⟩ ←
    core.iter.traits.double_ended.DoubleEndedIterator.rfold.trait_default.spec_list
      (iter_rfold.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT Std.U32)
      iter_rfold.rfold_slice_last.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U32U32
      (fun s => (s.slice.val.drop s.i).reverse) (fun _ x => x)
      ⟨(Array.make 3#usize [1#u32, 2#u32, 3#u32]).to_slice, 0⟩ 0#u32 ()
      (by
        intro s
        apply WP.spec_mono (core.slice.iter.IteratorSliceIter.next_back.spec_remaining s)
        intro r hr
        cases h : (s.slice.val.drop s.i).reverse <;> simpa [h] using hr)
      hcall
  simp [Array.to_slice, Array.make, hvalue, massert, WP.spec_ok]

theorem rev_fold_override : iter_rfold.rev_fold_override ⦃ r => r = () ⦄ := by
  unfold iter_rfold.rev_fold_override
  simp only [step_simps]
  let* ⟨r, r_post⟩ ← core.iter.traits.iterator.Iterator.rev.trait_default.spec
  let* ⟨value, value_post⟩ ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold.spec
      iter_rfold.Odd.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorU32
      iter_rfold.rev_fold_override.closure.Insts.CoreOpsFunctionFnMutPairU32U32U32
      r 0#u32 () (fun v => v = 99#u32)
      (by
        simp [iter_rfold.Odd.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorU32.rfold,
          iter_rfold.rev_fold_override.closure.Insts.CoreOpsFunctionFnMutPairU32U32U32.call_mut]
        step*)
  simp [value_post, massert, WP.spec_ok]

end IterFoldSpec
