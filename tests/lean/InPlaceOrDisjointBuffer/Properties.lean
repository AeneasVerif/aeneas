import Aeneas
import InPlaceOrDisjointBuffer.InPlaceOrDisjointBuffer
open Aeneas Aeneas.Std Aeneas.SepLogic WP Result

namespace in_place_or_disjoint_buffer

@[step]
theorem InPlaceOrDisjointBuffer.new_in_place.spec {T : Type} [ByteRepr T] (buf : Slice T) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.new_in_place buf
    ⦃⇓ r => ⌜r.1.src = r.1.dst.toConst ∧ r.1.len.val = buf.length ∧
      ∀ b values, values.length = buf.length →
        ⦃ r.1.dst ↦* values ⦄ r.2 b ⦃⇓ buf' => ⌜buf'.val = values⌝⦄⌝ ∗ r.1.dst ↦* buf.val ⦄ := by
  unfold InPlaceOrDisjointBuffer.new_in_place
  step*
  refine ⟨by simp, fun _ values h => Slice.end_as_mut_ptr.spec buf ptr values h⟩

@[step]
theorem InPlaceOrDisjointBuffer.impl.dst.spec {T : Type} [ByteRepr T] (b : InPlaceOrDisjointBuffer T) (s : Slice T)
    (hLength : s.length = b.len.val) :
    ⦃ b.dst ↦* s.val ⦄ InPlaceOrDisjointBuffer.impl.dst b
    ⦃⇓ r => ⌜r.1 = s ∧
      (∀ (old s' : Slice T), s'.length = old.length → old.length = b.len.val →
        ⦃ b.dst ↦* old.val ⦄ r.2.1 s' ⦃⇓ b' => ⌜b' = b⌝ ∗ b.dst ↦* s'.val ⦄) ∧
      (∀ b', r.2.2 b' = b)⌝ ∗ b.dst ↦* s.val ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.dst
  step*
  refine ⟨s_post, fun old s' h1 h2 => ?_, fun _ => trivial⟩
  have hBack := s_post1 old s' h1 h2
  step*

@[step]
theorem InPlaceOrDisjointBuffer.impl.len.spec {T : Type} [ByteRepr T] (b : InPlaceOrDisjointBuffer T) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.impl.len b ⦃⇓ r => ⌜r = b.len⌝ ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.len
  step*

theorem zero_first_in_place.spec (buf : Slice U8) (h : 0 < buf.length) :
    ⦃ emp ⦄ zero_first_in_place buf
    ⦃⇓ r => ⌜r.1.val = buf.length ∧ r.2.val = buf.val.set 0 0#u8⌝ ⦄ := by
  unfold zero_first_in_place
  step*

@[step]
theorem InPlaceOrDisjointBuffer.new_disjoint_from_slices.spec {T : Type} [ByteRepr T] (src dst : Slice T)
    (h : src.length = dst.length) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.new_disjoint_from_slices src dst
    ⦃⇓ r => ⌜r.1.len.val = src.length ∧
      ∀ b values, values.length = dst.length →
        ⦃ r.1.src ↦* src.val ∗ r.1.dst ↦* values ⦄ r.2 b
        ⦃⇓ dst' => ⌜dst'.val = values⌝⦄⌝ ∗ r.1.src ↦* src.val ∗ r.1.dst ↦* dst.val ⦄ := by
  unfold InPlaceOrDisjointBuffer.new_disjoint_from_slices
  step*
  refine ⟨by simp, fun _ values hv => ?_⟩
  step*

@[step]
theorem InPlaceOrDisjointBuffer.impl.src.spec {T : Type} [ByteRepr T] (b : InPlaceOrDisjointBuffer T) (s : Slice T)
    (hLength : s.length = b.len.val) :
    ⦃ b.src ↦* s.val ⦄ InPlaceOrDisjointBuffer.impl.src b
    ⦃⇓ r => ⌜r = s⌝ ∗ b.src ↦* s.val ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.src
  step*

theorem copy_first.spec (src dst : Slice U8) (h : src.length = dst.length) (h0 : 0 < src.length) :
    ⦃ emp ⦄ copy_first src dst ⦃⇓ r => ⌜r.val = dst.val.set 0 src.val[0]!⌝ ⦄ := by
  unfold copy_first
  step*

theorem write_through_raw_ptr.spec (x : Slice U8) (h : 0 < x.length) :
    ⦃ emp ⦄ write_through_raw_ptr x ⦃⇓ r => ⌜r.val = x.val.set 0 1#u8⌝ ⦄ := by
  unfold write_through_raw_ptr
  step*

end in_place_or_disjoint_buffer
