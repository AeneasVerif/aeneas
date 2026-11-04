module

public import RawMatrixView.Properties
public import RawScale.Notation
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_matrix_view

theorem scale_tail.spec (k : U32) (p : RawPtr Matrix) (matrix : Matrix) :
    ⦃ alloc matrixRepr p p.address 1 false ∗ pointsTo matrixRepr p p.address matrix ⦄
    (do let result ← scale_raw matrixRepr k p
        let matrix ← core.ptr.end_from_mut matrixRepr p
        pure (result, matrix))
    ⦃ (result : U32) (updated : Matrix) => fun h =>
      result = (scaledMatrix k matrix).val[1]!.val[12]! ∧
      updated = scaledMatrix k matrix ∧ empty h ⦄ := by
  intro h F s₀ hp hd hm hi
  have kernel := HeapWP.frame (R := alloc matrixRepr p p.address 1 false)
    (scale_raw.spec k p p.address matrix)
  apply HeapWP.Spec.bind (kernel h F s₀ ((sep_comm _ _ _).mp hp) hd hm hi)
  rintro result s₁ ⟨h₁, hd₁, hm₁, hi₁, post⟩
  obtain ⟨hr, hp₁⟩ := (sep_and_left _ _ _ h₁).mp post
  have restored := (sep_comm _ _ _).mp
    (sep_mono (fun _ => pointsTo_readable) (fun _ hp => hp) hp₁)
  apply HeapWP.Spec.bind (HeapWP.end_from_mut.spec matrixRepr p p.address
    (scaledMatrix k matrix) (by decide) h₁ F s₁ restored hd₁ hm₁ hi₁)
  rintro updated s₂ ⟨h₂, hd₂, hm₂, hi₂, hu, hemp⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h₂, hd₂, hm₂, hi₂, hr, hu, hemp⟩

/-- **Spec theorem for `raw_matrix_view::scale`**
    The nested flat borrow is returned before the aggregate read; the outer
    backward computation then returns the scaled safe matrix and retires its
    exposure. The returned scalar is the last logical element. -/
theorem scale.spec (k : U32) (matrix : Matrix) (s₀ : Heap) (F : Fragment)
    (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (scale matrixRepr k matrix)
      (fun (result, updated) s₁ =>
        result = (scaledMatrix k matrix).val[1]!.val[12]! ∧
        updated = scaledMatrix k matrix ∧ Fragment.Matches s₁ F ∧ s₁.Inv) s₀ := by
  simp only [scale, core.ptr.from_mut, Aeneas.Std.bind_assoc, bind_ok]
  apply HeapWP.Spec.bind (HeapWP.allocExposure_encoded.spec matrixRepr matrix
    (matrixRepr_calibrated matrix) s₀ F hi hm)
  rintro p s₁ ⟨_, h, hd, hm₁, hi₁, hp⟩
  apply HeapWP.Spec.mono (scale_tail.spec k p matrix h F s₁ hp hd hm₁ hi₁)
  rintro ⟨result, updated⟩ s₂ ⟨h₂, _, hm₂, hi₂, hr, hu, rfl⟩
  exact ⟨hr, hu, by simpa using hm₂, hi₂⟩

end raw_matrix_view
