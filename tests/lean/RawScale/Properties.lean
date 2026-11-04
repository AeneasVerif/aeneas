module

public import RawScale.Funs
public import RawScale.RangeAccess
public import RawMatrixView.Properties
public import Aeneas.Std.RangeIter
import all RawScale.Funs
import all RawMatrixView.Funs

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_scale

set_option maxHeartbeats 1000000

/- The safe loops have identical emitted bodies; this checked equality lets us
   reuse the completed proof without duplicating it or replacing the algorithm. -/
unseal scale_slice_loop raw_matrix_view.scale_slice_loop in
theorem scale_slice_eq (k : U32) (buf : Slice U32) :
    scale_slice k buf = raw_matrix_view.scale_slice k buf := by
  rfl

/-- **Spec theorem for `raw_scale::scale_slice`**
    All physical lanes are multiplied exactly under the non-overflow bound. -/
@[step]
theorem scale_slice.spec (k : U32) (buf : Slice U32)
    (hbound : ∀ j, j < buf.length → k.val * buf[j]!.val ≤ U32.max) :
    scale_slice k buf ⦃ (result : Slice U32) =>
      result.val.map UScalar.val = buf.val.map (fun x => k.val * x.val) ⦄ := by
  rw [scale_slice_eq]
  exact raw_matrix_view.scale_slice.spec k buf hbound

theorem scale_slice.values (k : U32) (buf : Slice U32) :
    scale_slice k buf ⦃ (result : Slice U32) =>
      result.val = buf.val.map (core.num.U32.wrapping_mul k) ⦄ := by
  rw [scale_slice_eq]
  exact raw_matrix_view.scale_slice.values k buf

/-- **Spec theorem for zero-length `raw_scale::scale_raw`**
    No pointer operation occurs, even for pointers without a live allocation. -/
theorem scale_raw_zero (k : U32) (src : ConstRawPtr U32) (dst : MutRawPtr U32) :
    scale_raw 0#usize k src dst ⦃ (_ : Unit) => True ⦄ := by
  unfold scale_raw scale_raw_loop
  step*

def scaleStep (k : U32) (src : ConstRawPtr U32) (dst : MutRawPtr U32)
    (i : Usize) : Result Unit := do
  let p ← RawPtr.add raw_box.u32Repr src i
  let p1 ← RawPtr.add raw_box.u32Repr dst i
  scale_one_raw k p p1

private theorem fold_scaleStep (k : U32) (src : ConstRawPtr U32) (dst : MutRawPtr U32)
    (i : Usize) (next : Result Unit) :
    (do
      let p ← RawPtr.add raw_box.u32Repr src i
      let p1 ← RawPtr.add raw_box.u32Repr dst i
      scale_one_raw k p p1
      next) =
    (do scaleStep k src dst i; next) := by
  simp only [scaleStep, bind_tc_eq, Aeneas.Std.bind_assoc]

/-- Framed loop rule for the actual extracted iterator and scalar operations.
    A concrete disjoint/equal invariant must still discharge `body`. -/
theorem scale_raw_loop.rule (N : Usize) (k : U32)
    (src : ConstRawPtr U32) (dst : MutRawPtr U32)
    (iter : core.ops.range.Range Usize) (I : Nat → SepLogic.Assertion)
    (hend : iter.end = N) (hle : iter.start.val ≤ N.val)
    (body : ∀ i : Usize, i.val < N.val →
      HeapWP.Triple (I i.val) (scaleStep k src dst i) (fun _ => I (i.val + 1))) :
    HeapWP.Triple (I iter.start.val) (scale_raw_loop iter k src dst)
      (fun _ => I N.val) := by
  intro h F s hp hd hm hinv
  unfold scale_raw_loop
  by_cases hlt : iter.start.val < iter.end.val
  · apply HeapWP.Spec.bind
      (HeapWP.Spec.of_spec (core.iter.range.IteratorRange.next_Usize_some_spec iter hlt) s)
    intro result s₁ hnext
    obtain ⟨o, iter₁⟩ := result
    obtain ⟨⟨ho, hstart, hend₁⟩, hs⟩ := hnext
    subst o
    subst s₁
    change HeapWP.Spec (do
      let p ← RawPtr.add raw_box.u32Repr src iter.start
      let p1 ← RawPtr.add raw_box.u32Repr dst iter.start
      scale_one_raw k p p1
      scale_raw_loop iter₁ k src dst) _ s
    have folded := fold_scaleStep k src dst iter.start (scale_raw_loop iter₁ k src dst)
    simp only [bind_tc_eq] at folded
    rw [folded]
    have ih := scale_raw_loop.rule N k src dst iter₁ I
      (hend₁.trans hend) (by agrind) body
    have rest : HeapWP.Triple (I (iter.start.val + 1))
        (scale_raw_loop iter₁ k src dst) (fun _ => I N.val) := by
      simpa only [hstart] using ih
    exact HeapWP.Triple.bind (body iter.start (by agrind)) (fun _ => rest)
      h F s hp hd hm hinv
  · apply HeapWP.Spec.bind
      (HeapWP.Spec.of_spec (core.iter.range.IteratorRange.next_Usize_none_spec iter (by agrind)) s)
    intro result s₁ hnext
    obtain ⟨o, iter₁⟩ := result
    obtain ⟨⟨ho, _⟩, hs⟩ := hnext
    subst o
    subst s₁
    apply (HeapWP.Spec.pure () _ s).mpr
    exact ⟨h, hd, hm, hinv, by simpa only [show iter.start.val = N.val by agrind] using hp⟩
termination_by N.val - iter.start.val
decreasing_by agrind

/-- Instantiates the extracted loop rule at its actual zero-based iterator. -/
theorem scale_raw.rule (N : Usize) (k : U32)
    (src : ConstRawPtr U32) (dst : MutRawPtr U32) (I : Nat → SepLogic.Assertion)
    (body : ∀ i : Usize, i.val < N.val →
      HeapWP.Triple (I i.val) (scaleStep k src dst i) (fun _ => I (i.val + 1))) :
    HeapWP.Triple (I 0) (scale_raw N k src dst) (fun _ => I N.val) := by
  unfold scale_raw
  simpa using scale_raw_loop.rule N k src dst ⟨0#usize, N⟩ I rfl (by simp) body

def scaledWords (k : U32) (initial : Vector U32 count) : Vector U32 count :=
  initial.map (core.num.U32.wrapping_mul k)

theorem scaledWords_values (k : U32) (initial : Vector U32 count)
    (hbound : ∀ j, j < count → k.val * initial[j]!.val ≤ U32.max) :
    (scaledWords k initial).map UScalar.val =
      initial.map (fun value => k.val * value.val) := by
  rw [scaledWords, Vector.map_map]
  apply Vector.ext
  intro j hj
  have hb : k.val * initial[j].val ≤ U32.max := by simpa [hj] using hbound j hj
  simp only [Vector.getElem_map, Function.comp_apply, core.num.U32.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

theorem scaledWords_zero (k : U32) (initial : Vector U32 count) (j : Fin count)
    (hz : initial[j.val]'j.isLt = 0#u32) :
    (scaledWords k initial)[j.val]'j.isLt = 0#u32 := by
  rw [scaledWords, Vector.getElem_map, hz]
  apply UScalar.eq_of_val_eq
  simp [core.num.U32.wrapping_mul_val_eq]

/-- **Spec theorem for `raw_scale::scale_via_borrow_raw`**
    The matching backward function restores all sixteen updated words before
    the final raw read. The complete range and an arbitrary frame survive. -/
theorem scale_via_borrow_raw.spec (k : U32) (p : MutRawPtr U32) (base : BasePtr)
    (initial : Vector U32 16) :
    HeapWP.Triple (SepLogic.pointsToRange raw_box.u32Repr p base initial)
      (scale_via_borrow_raw k p)
      (fun result h => result = (scaledWords k initial)[0] ∧
        SepLogic.pointsToRange raw_box.u32Repr p base (scaledWords k initial) 0 h) := by
  intro h F s₀ hp hd hm hinv
  have fits : initial.toList.length ≤ Usize.max := by scalar_tac
  unfold scale_via_borrow_raw core.slice.raw.from_raw_parts_mut RawPtr.borrowSlice
  simp only [bind_tc_eq, bind_ok, Aeneas.Std.bind_assoc]
  have count_eq : (16#usize).val = 16 := by simp
  rw [count_eq]
  have noPointers : ∀ i : Fin 16, ∀ q,
      ¬ raw_box.u32Repr.Carries ((scaledWords k initial)[i.val]'i.isLt) q := by
    intro i q
    exact raw_box.u32Repr_noPointers _ q
  have borrowed := HeapWP.borrowRange_return.spec raw_box.u32Repr p base
    initial (scaledWords k initial) noPointers (by decide) (by decide)
    h F s₀ hp hd hm hinv
  apply HeapWP.Spec.bind borrowed
  intro values s₁ hborrow
  obtain ⟨hvalues, returns⟩ := hborrow
  rw [hvalues]
  simp only [dite_eq_left fits, bind_ok]
  apply HeapWP.Spec.bind (HeapWP.Spec.of_spec (scale_slice.values k _) s₁)
  rintro scaled s₂ ⟨hscaled, rfl⟩
  have hs : scaled.val = (scaledWords k initial).toList := by
    simpa only [scaledWords, Vector.toList_map, Slice.from_val] using hscaled
  have hlen : scaled.length = (16#usize).val := by
    change scaled.val.length = (16#usize).val
    rw [hs]
    simp
  unfold core.slice.raw.from_raw_parts_mut.back
  rw [ite_eq_left hlen, hs]
  apply HeapWP.Spec.bind returns
  rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  exact read_range.spec raw_box.u32Repr p p base (scaledWords k initial) 0
    ⟨0, by decide⟩ (by decide) rfl (by simp) h₂ F s₂ hp₂ hd₂ hm₂ hi₂

end raw_scale
