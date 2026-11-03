module

public import RawMatrixView.Funs
public import RawMatrixView.Layout
public import Aeneas.Std.Heap.RangeRestoration
public import Aeneas.Std.Scalar.WrappingOps.Mul
import all RawMatrixView.Funs

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_matrix_view

set_option maxHeartbeats 1000000

private theorem wrapping_mul_exact (k value : U32)
    (hbound : k.val * value.val ≤ U32.max) :
    lift (core.num.U32.wrapping_mul k value) ⦃ (result : U32) =>
      result.val = k.val * value.val ⦄ := by
  step as ⟨result, hresult⟩
  rw [hresult, core.num.U32.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- **Spec theorem for `raw_matrix_view::scale_slice`'s loop**
    The prefix is unchanged and the suffix is multiplied exactly, without overflow. -/
@[step]
theorem scale_slice_loop.spec (k : U32) (values : Slice U32) (i : Usize)
    (hi : i.val ≤ values.length)
    (hbound : ∀ j, i.val ≤ j → j < values.length →
      k.val * values[j]!.val ≤ U32.max) :
    scale_slice_loop k values i ⦃ (result : Slice U32) =>
      result.length = values.length ∧
      ∀ j, j < result.length →
        result[j]!.val = if j < i.val then values[j]!.val else k.val * values[j]!.val ⦄ := by
  unfold scale_slice_loop
  simp only [step_simps]
  spec_split
  · let* ⟨ i2, i2_post ⟩ ← Slice.index_usize_spec
    let* ⟨ i3, i3_post ⟩ ← wrapping_mul_exact
    · have hb := hbound i.val (by agrind) (by agrind)
      simp_lists [i2_post] at *
      agrind
    let* ⟨ s, s_post ⟩ ← Slice.update_spec
    let* ⟨ i4, i4_post ⟩ ← Usize.add_spec
    let* ⟨ result, result_post, result_post1 ⟩ ← spec
    · simp_lists [s_post, i4_post]
      agrind
    split_conjs
    · agrind
    · intro j hj
      have hr := result_post1 j hj
      simp_lists [s_post, i4_post] at hr
      by_cases he : j = i.val
      · subst j
        simp_lists [i3_post, i2_post] at hr
        have hrl : i.val < result.val.length := by agrind
        have hvl : i.val < values.val.length := by agrind
        simpa [Slice.getElem!_Nat_eq, hrl, hvl] using hr
      · simp_lists [he] at hr
        have hrl : j < result.val.length := by agrind
        have hvl : j < values.val.length := by agrind
        have hcmp : (j < i.val + 1) = (j < i.val) := by agrind
        simpa [Slice.getElem!_Nat_eq, hrl, hvl, hcmp] using hr
  · simp only [step_simps]
    agrind
termination_by values.length - i.val
decreasing_by scalar_decr_tac

/-- **Spec theorem for `raw_matrix_view::scale_slice`**
    All entries are multiplied exactly under the non-overflow bound. -/
@[step]
theorem scale_slice.spec (k : U32) (values : Slice U32)
    (hbound : ∀ j, j < values.length → k.val * values[j]!.val ≤ U32.max) :
    scale_slice k values ⦃ (result : Slice U32) =>
      result.val.map UScalar.val = values.val.map (fun x => k.val * x.val) ⦄ := by
  unfold scale_slice
  step as ⟨result, hlen, hvalues⟩
  apply List.ext_getElem
  · simp [hlen]
  · intro j hj hj'
    have hv := hvalues j (by simpa using hj)
    have hr : j < result.val.length := by simpa using hj
    have hi : j < values.val.length := by simpa using hj'
    simpa [Slice.getElem!_Nat_eq, hr, hi] using hv

unseal Result in
theorem scale_slice_loop.wrapping_spec (k : U32) (values : Slice U32) (i : Usize)
    (hi : i.val ≤ values.length) :
    scale_slice_loop k values i ⦃ (result : Slice U32) =>
      result.length = values.length ∧
      ∀ j, j < result.length →
        result[j]! = if j < i.val then values[j]!
          else core.num.U32.wrapping_mul k values[j]! ⦄ := by
  unfold scale_slice_loop
  simp only [step_simps]
  spec_split
  · let* ⟨value, hvalue⟩ ← Slice.index_usize_spec
    simp only [lift, bind_ok]
    let* ⟨updated, hupdated⟩ ← Slice.update_spec
    let* ⟨next, hnext⟩ ← Usize.add_spec
    let* ⟨result, hlen, hresult⟩ ← wrapping_spec
    split_conjs
    · agrind
    · intro j hj
      have hr := hresult j hj
      simp_lists [hupdated, hnext] at hr
      by_cases he : j = i.val
      · subst j
        have hrl : i.val < result.val.length := by agrind
        have hvl : i.val < values.val.length := by agrind
        simpa [hvalue, Slice.getElem!_Nat_eq, hrl, hvl] using hr
      · simp_lists [he] at hr
        have hrl : j < result.val.length := by agrind
        have hvl : j < values.val.length := by agrind
        have hcmp : (j < i.val + 1) = (j < i.val) := by agrind
        simpa [Slice.getElem!_Nat_eq, hrl, hvl, hcmp] using hr
  · simp only [step_simps]
    agrind
termination_by values.length - i.val
decreasing_by scalar_decr_tac

/-- The safe helper computes wrapping products for every input, including overflow. -/
theorem scale_slice.values (k : U32) (values : Slice U32) :
    scale_slice k values ⦃ (result : Slice U32) =>
      result.val = values.val.map (core.num.U32.wrapping_mul k) ⦄ := by
  unfold scale_slice
  apply WP.spec_mono (scale_slice_loop.wrapping_spec k values 0#usize (by simp))
  rintro result ⟨hlen, hvalues⟩
  apply List.ext_getElem
  · simp [hlen]
  · intro j hr hj
    have hv : j < values.val.length := by simpa using hj
    simpa [Slice.getElem!_Nat_eq, hr, hv] using hvalues j (by simpa using hr)

unseal Result

private theorem pure_spec_heap {α : Type} {c : Result α} {P : α → Prop}
    (hc : WP.spec c P) (s : Heap) :
    HeapWP.Spec c (fun result s' => P result ∧ s' = s) s := by
  cases c
  · rename_i result
    exact (HeapWP.Spec.pure result _ s).mpr ⟨(WP.spec_ok result).mp hc, rfl⟩
  · exact (WP.spec_vis _ _ |>.mp hc).elim
  · exact (WP.spec_div.mp hc).elim

private theorem last_spec (m : Matrix) :
    (do
      let a ← Array.index_usize m 1#usize
      Array.index_usize a 12#usize) ⦃ (result : U32) =>
        result = m.val[1]!.val[12]! ⦄ := by
  step*
  · simp [*]

def scaledMatrix (k : U32) (m : Matrix) : Matrix :=
  ofWords ((words m).map (core.num.U32.wrapping_mul k))

theorem scaledMatrix_values (k : U32) (initial : Matrix)
    (hbound : ∀ j, j < 32 → k.val * (words initial)[j]!.val ≤ U32.max) :
    (words (scaledMatrix k initial)).map UScalar.val =
      (words initial).map (fun value => k.val * value.val) := by
  rw [scaledMatrix, words_ofWords, Vector.map_map]
  apply Vector.ext
  intro j hj
  have hb : k.val * (words initial)[j].val ≤ U32.max := by
    simpa [hj] using hbound j hj
  simp only [Vector.getElem_map, Function.comp_apply, core.num.U32.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

def zeroPadded (m : Matrix) : Prop :=
  ∀ j : Fin 32, 13 ≤ j.val % 16 → (words m)[j.val]'j.isLt = 0#u32

theorem scaledMatrix_zeroPadded (k : U32) (initial : Matrix)
    (hzero : zeroPadded initial) : zeroPadded (scaledMatrix k initial) := by
  intro j hj
  rw [scaledMatrix, words_ofWords, Vector.getElem_map, hzero j hj]
  apply UScalar.eq_of_val_eq
  simp [core.num.U32.wrapping_mul_val_eq]

open SepLogic

/-- **Spec theorem for `raw_matrix_view::scale_raw`**
    The matched backward call restores all 32 scaled words before the aggregate
    read, preserving an arbitrary disjoint frame. `scaledMatrix_values` gives
    ordinary multiplication and `scaledMatrix_zeroPadded` preserves hidden zeros. -/
theorem scale_raw.spec (k : U32) (p : MutRawPtr Matrix) (base : BasePtr)
    (initial : Matrix) :
    HeapWP.Triple (pointsTo matrixRepr p base initial)
      (scale_raw matrixRepr k p)
      (fun result h => result = (scaledMatrix k initial).val[1]!.val[12]! ∧
        pointsTo matrixRepr p base (scaledMatrix k initial) 0 h) := by
  intro h F s₀ hp hd hm hinv
  have aligned : 32 ∣ p.address.val := by
    obtain ⟨_, _, _, aligned, _⟩ := hp
    exact aligned
  have hpWords := matrix_to_words p base initial h hp
  let updated := (words initial).map (core.num.U32.wrapping_mul k)
  have fits : (words initial).toList.length ≤ Usize.max := by scalar_tac
  unfold scale_raw core.ptr.mut_ptr.RawPtrMutT.cast
  unfold core.slice.raw.from_raw_parts_mut RawPtr.borrowSlice
  simp only [bind_tc_eq, bind_ok, Aeneas.Std.bind_assoc]
  have count_eq : (32#usize).val = 32 := by simp
  rw [count_eq]
  have noPointers : ∀ i : Fin 32, ∀ q, ¬ raw_box.u32Repr.Carries (updated[i.val]'i.isLt) q := by
    intro i q
    exact raw_box.u32Repr_noPointers _ q
  have borrowed := HeapWP.borrowRange_return.spec raw_box.u32Repr
    (p.cast U32) base (words initial) updated
    noPointers (by decide) (by decide) h F s₀ hpWords hd hm hinv
  apply HeapWP.Spec.bind borrowed
  intro values s₁ hborrow
  obtain ⟨hvalues, returns⟩ := hborrow
  rw [hvalues]
  simp only [dite_eq_left fits, bind_ok]
  apply HeapWP.Spec.bind (pure_spec_heap (scale_slice.values k _) s₁)
  rintro scaled s₂ ⟨hscaled, rfl⟩
  have hs : scaled.val = updated.toList := by
    simpa only [updated, Vector.toList_map, Slice.from_val] using hscaled
  have hlen : scaled.length = (32#usize).val := by
    change scaled.val.length = (32#usize).val
    rw [hs]
    simp
  unfold core.slice.raw.from_raw_parts_mut.back
  rw [ite_eq_left hlen, hs]
  apply HeapWP.Spec.bind returns
  rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  have restored := words_to_matrix p base updated h₂ aligned hp₂
  apply HeapWP.Spec.bind
    (HeapWP.read.spec matrixRepr p base (ofWords updated) 0 (by decide)
      h₂ F s₂ restored hd₂ hm₂ hi₂)
  rintro m s₃ ⟨h₃, hd₃, hm₃, hi₃, rfl, hp₃⟩
  apply HeapWP.Spec.mono (pure_spec_heap (last_spec _) s₃)
  rintro result s₄ ⟨hr, rfl⟩
  exact ⟨h₃, hd₃, hm₃, hi₃, hr, hp₃⟩

end raw_matrix_view
